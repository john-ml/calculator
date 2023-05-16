import lark as L
import networkx as N

# Global poset on cursor positions used by pretty-printer (see help(mixfix))
from preorder import Preorder
global_prec_order = Preorder().add_bot('bot').add_top('top')
parser_up_to_date = True
def to_prec(p): return p.__name__ if type(p) is type else p
def add_prec(p):
  global_prec_order.add(to_prec(p))
  parser_up_to_date = False
def prec_ge(p, q):
  global_prec_order.add_le(to_prec(q), to_prec(p))
  parser_up_to_date = False
def prec_ges(pqs):
  for p, q in pqs:
    prec_ge(p, q)
  parser_up_to_date = False
def prec_bot(p):
  global_prec_order.add_bot(to_prec(p))
  parser_up_to_date = False
def prec_top(p):
  global_prec_order.add_top(to_prec(p))
  parser_up_to_date = False

# ---------- Name binding ----------

def nats():
  n = 0
  while True:
    yield n
    n += 1
global_nats = nats()

class Name:
  '''
  Names are represented as pairs (x:str, n:nat).
  - x is the 'pretty name', usually specified by the user
  - n is a disambiguator used to ensure that bound variables are never shadowed
  '''
  def __init__(self, x, n=None):
    self.x = x
    self.n = n
  def __hash__(self): return hash((self.x, self.n))
  def __eq__(self, other): return self.x == other.x and self.n == other.n
  def __repr__(self): return f'Name({self.x}, {self.n})'
  def __str__(self): return self.x if self.n is None else f'{self.x}@{self.n}'
  def fresh(self): return Name(self.x, next(global_nats))
  def with_n(self, n): return Name(self.x, n)

class V:
  '''
  An occurrence of a variable name.
  Usually not used to construct variables explicitly; see help(F).
  '''
  __match_args__ = ('x',)
  def __init__(self, x): self.x = x
  def __eq__(self, other, renaming={}): return renaming[self.x] == other.x if self.x in renaming else self.x == other.x
  def __repr__(self): return f'V({repr(self.x)})'
  def __str__(self): return self.str(None)
  def fresh(self, renaming={}): return V(renaming[self.x]) if self.x in renaming else self
  def subst(self, substitution): return substitution[self.x] if self.x in substitution else self
  def simple_names(self, renaming={}, in_use=None): return V(renaming[self.x]) if self.x in renaming else self
  def fvs(self): return {self.x}
  def no_parens(self): return self
  def str(self, mode, left_prec='bot', right_prec='bot', prec_order=global_prec_order): return str(self.x)

class F:
  '''
  A binding form. There are two ways to construct instances of F:
  - F('x', lambda x: e[x]) represents a term e with free variable x.
    Constructs a value F(Name('x', n), e[V(Name('x', n))]) with n fresh.
  - F(x:Name, e) represents a term e with free variable x.
    Does not do any freshening.
  Pattern matching against an instance of F produces [x:Name, e:term] with x fresh.
  Therefore, while F instances are constructed by F('x', lambda x: e) and F(x, e),
  they are pattern-matched against as F([x, e]). This is to ensure that the
  fresh name and its body are extracted together. To support pattern F(x, e) would
  require two different getters for the name and the body. Depending on the order
  in which the getters are called during pattern matching, this could cause e to
  be scoped with respect to a stale version of x.
  '''
  __match_args__ = ('unwrap',)
  def __init__(self, x, e=None):
    fn = type(lambda x: x)
    if type(x) is str and type(e) is type(lambda x: x):
      self.x = Name(x).fresh()
      self.e = e(V(self.x))
    elif type(x) is Name:
      self.x = x
      self.e = e
    else:
      raise ValueError(f'F({repr(x)}, {repr(e)})')

  def __repr__(self):
    return f'F({repr(self.x)}, {repr(self.e)})'
  
  def __eq__(self, other, renaming={}):
    return type(other) is F and self.e.__eq__(other.e, renaming | {self.x: other.x})

  def __str__(self): return self.str(None)

  def fresh(self, renaming={}):
    x = self.x.fresh()
    e = self.e.fresh(renaming | {self.x: x})
    return F(x, e)

  def subst(self, substitution):
    x = self.x.fresh()
    e = self.e.subst(substitution | {self.x: V(x)})
    return F(x, e)

  def simple_names(self, renaming={}, in_use=None):
    if in_use is None: in_use = set(v for _, v in renaming.items())
    banned = in_use | self.fvs()
    x = (
      self.x.with_n(None) if self.x.with_n(None) not in banned else
      next(self.x.with_n(n) for n in nats() if self.x.with_n(n) not in banned)
    )
    e = self.e.simple_names(renaming | {self.x: x}, in_use | {x})
    return F(x, e)

  def fvs(self):
    return self.e.fvs() - {self.x}

  def no_parens(self): return F(self.x, self.e.no_parens())

  def get_unwrap(self):
    e = self.fresh()
    res = [e.x, e.e]
    return res
  def set_unwrap(self): assert False
  unwrap = property(get_unwrap, set_unwrap)

  def str(self, mode, left_prec='bot', right_prec='bot', prec_order=global_prec_order):
    dot = '.' if mode is None else '. '
    return f"{str(self.x)}{dot}{self.e.str(mode, left_prec='bot', right_prec=right_prec, prec_order=prec_order)}"


# ---------- Mixfix decorator ----------

def parens(s): return f'({s})'

class Str:
  r'''
  Helper class used to specify string literals in mixfix declarations.
  S(s) specifies the string literal s is to be used in parsing and pretty-printing with
  .str(). Optionally, one can specify different string literals to be used for
  different modes (e.g. to parse \x.e as a lambda term and pretty-print it in
  LaTeX with \lambda) via keyword arguments. Concretely, S(s, pretty=t) declares
  a string literal s for parsing and t for .str('pretty').

  For example use of S see help(mixfix).
  '''
  def __init__(self, s, **kwargs):
    self.s = s
    self.kvs = kwargs

  def in_mode(self, mode):
    if mode is None or mode not in self.kvs: return self.s
    else: return self.kvs[mode]

  def modes(self): return tuple(m for m in self.kvs)

# Parser of highly ambiguous grammar updated by each invocation of @mixfix.
def make_parser():
  # Annoyingly, lark nonterminals must contain only lowercase letters.
  # So munge class names to fit this format. Assumes no class names contain _
  def classname_to_nt(s): return 'c' + ''.join('_' + c.lower() if c.isupper() else c for c in s)
  def nt_to_classname(s): return ''.join('' if c == '_' else c.upper() if prev == '_' else c for (prev, c) in zip(s[1:], s[2:]))
  # The grammar is stored as a list of productions. A production like
  #   @mixfix
  #   class Add:
  #     m: any
  #     plus: Str('+')
  #     n: any
  # is represented as the tuple
  #   (C, [('m', any), ('plus', '+'), ('n', any)])
  def make_grammar(ps):
    # Naive version of make_fancy_grammar() that puts all productions into a
    # single nonterminal 'term'. Not used but could come in handy for debugging.
    escape = lambda s: f'"{repr(s)[1:-1]}"'
    def make_prod_item(s):
      if s is F:
        return 'name "." term'
      elif type(s) is str:
        return '' if s == '' else escape(s)
      else:
        return 'term'
    lines = ''.join(
      f'\n      | {" ".join(make_prod_item(s) for _, s in p)} -> {classname_to_nt(c.__name__)}' for c, p in ps
    )
    return f'''
      ?term : atom{lines}
  
      ?atom : name -> var
      | ESCAPED_STRING -> string
      | SIGNED_NUMBER -> number
      | "(" term ")" -> parens

      name : CNAME
  
      %import common.CNAME
      %import common.ESCAPED_STRING
      %import common.SIGNED_NUMBER
      %import common.WS
      %ignore WS
    '''
  def make_fancy_grammar(prec_order, ps):
    # Constructs the grammar more intelligently than make_grammar() by using the
    # precedence poset to cut down the number of ambiguities. Essentially each
    # (left-cursor-position, right-cursor-position) pair becomes a nonterminal
    # that only references nonterminals corresponding to cursor positions that
    # are higher up in the poset. Incomparable connected components of the
    # precedence poset should produce completely independent grammars, and
    # annotations enforcing operator precedence and associativity should produce
    # properly-factored ones.
    #
    # General idea: generate
    #   bot_bot : p_q for each successor (p,q) of (bot,bot) in poset
    #   p_q : p_r s t_q for each production with left and right precs (p,q) and intermediate precs r,t
    #       | p'_q' for each successor (p',q') of (p,q) in poset
    #   ...
    #   top_top : atom | other top_top productions
    #
    #   atom : name | "(" bot_bot ")" | ...
    #
    # To achieve this:
    # - Let G be the graph that generates the precedence poset.
    # - Quotient G by SCCs to get a dag D.
    # - Confusing each element of G with its equivalence class, the product D^2
    #   orders pairs of precedences (l, r).
    # - The key operation we need is, given a pair (l, r), to find immediate
    #   successors (l', r') where l' and r' are valid left- and right-
    #   precedences of a production in ps.
    # - It'd be enough to have a graph with
    #     (l,r) -> (l',r') iff
    #       (l',r') are left- and right-precs for a production in ps
    #       and (l,r) ->+ (l',r') in D^2
    #       and there is no path (l,r) ->+ (l'',r'') ->+ (l',r')
    #       for (l'',r'') also valid left- and right-precs
    # - One way to compute this is to take the transitive closure (D^2)+ and cut
    #   it down to the subgraph with edges
    #       {lr->lr' | lr' valid left-right-precs}
    #       \ {lr->lr'' | lr->lr'->lr'' in (D^2)+ with lr', lr'' both valid left-right-precs}
    #   There is probably a more efficient way, but this is what's done for now.
    g = prec_order.generator_graph()
    partition = tuple(frozenset(scc) for scc in N.strongly_connected_components(g))
    canon = {x: eclass for eclass in partition for x in eclass}
    d = N.quotient_graph(g, partition, create_using=N.DiGraph)
    # To make ps easier to query, reorganize so that it maps pairs (l, r) to
    # productions whose left- and right-most cursor positions match l and r.
    ps_at = {}
    for p in ps:
      l, [*_, (r, _)] = p
      l = canon[to_prec(l)]
      r = canon[to_prec(r)]
      if (l, r) not in ps_at: ps_at[l, r] = []
      ps_at[l, r].append(p)
    # Compute transitive closure of D^2
    d2 = N.strong_product(d, d) # strong_product = includes edges (v,w),(v,w') for w->w' in D
    d2plus = N.transitive_closure(d2)
    # Compute graph giving nontrivial successors for any pair (l, r)
    lr_is_top = lambda lr: 'top' in lr[0] and 'top' in lr[1]
    lr_ok = lambda lr: lr in ps_at or lr_is_top(lr)
    prec_graph = d2plus.edge_subgraph(
      {(v, w) for v, w in d2plus.edges if lr_ok(w)}
      - {(u, w) for u, v in d2plus.edges if lr_ok(v) for w in d2plus.successors(v) if lr_ok(w)}
    )
    # Small optimization to clean up the generated grammar: if (l,r) has exactly
    # one successor (l',r') in prec_graph, replace (l,r) with (l',r') throughout.
    canon_lr = {}
    for lr in prec_graph.nodes:
      succs = tuple(prec_graph.successors(lr))
      if lr not in ps_at and len(succs) == 1: canon_lr[lr] = succs[0]
      else: canon_lr[lr] = lr
    # Associate each pair (l, r) : eclass^2 to a unique Lark-friendly identifier
    eclass_of_id = tuple(partition)
    id_of_eclass = {eclass: i for i, eclass in enumerate(eclass_of_id)}
    # str_of_lr = lambda l, r: f'term_{repr(set(l))}_{repr(set(r))}' # Useful for debugging
    make_lr = lambda s, t: canon_lr[canon[s], canon[t]]
    bot_lr = make_lr('bot', 'bot')
    def str_of_lr(lr):
      if lr == bot_lr: return 'term'
      l, r = lr
      return f'term_{id_of_eclass[l]}_{id_of_eclass[r]}'
    # Maps strings of the form str_of_lr(l, r) to a list of strings encoding productions
    productions = {} 
    # Populate productions by recursively traversing prec_graph
    def go(lr):
      nonlocal prec_order, productions, ps
      assert lr == canon_lr[lr]
      str_lr = str_of_lr(lr)
      if str_lr in productions: return
      productions[str_lr] = []
      if lr_is_top(lr):
        productions[str_lr].append('atom')
      for c, p in ps_at.get(lr, []):
        pieces = []
        for (new_l, _), (new_r, v) in zip([(to_prec(c), None)] + p, p):
          if type(v) is str:
            escape = lambda s: f'"{repr(s)[1:-1]}"'
            if v != '': pieces.append(escape(v))
          elif v is F:
            new_lr = make_lr('bot', new_r)
            pieces.append('name')
            pieces.append('"."')
            pieces.append(str_of_lr(new_lr))
            go(new_lr)
          else:
            new_lr = make_lr(new_l, new_r)
            pieces.append(str_of_lr(new_lr))
            go(new_lr)
        productions[str_lr].append(f'{" ".join(pieces)} -> {classname_to_nt(c.__name__)}')
      for next_lr in prec_graph.successors(lr):
        productions[str_lr].append(str_of_lr(canon_lr[next_lr]))
        go(next_lr)
    go(bot_lr)
    str_productions = '\n\n'.join(
      f'      ?{k} : ' + '\n      | '.join(p)
      for k, p in productions.items()
    )
    return f'''{str_productions}

      ?atom : name -> var
      | ESCAPED_STRING -> string
      | SIGNED_NUMBER -> number
      | "(" term ")" -> parens

      name : CNAME

      %import common.CNAME
      %import common.ESCAPED_STRING
      %import common.SIGNED_NUMBER
      %import common.WS
      %ignore WS
    '''
  def make_parser(grammar):
    print(grammar)
    return L.Lark(grammar, start='term', ambiguity='explicit')
  class Parens:
    '''
    An explicit parenthesization.
    Used only by the parser to match strings up to the insertion of superfluous
    parentheses. Removed (recursively) from syntax trees by no_parens(). Users
    should never see instances of this class.
    '''
    __match_args__ = ('x',)
    def __init__(self, x): self.x = x
    def __eq__(self, other): return self.x == other.x
    def __repr__(self): return f'Parens({repr(self.x)})'
    def __str__(self): return self.str(None)
    def fresh(self, renaming={}): assert False
    def subst(self, substitution): assert False
    def simple_names(self, renaming={}, in_use=None): assert False
    def fvs(self): assert False
    def no_parens(self): return self.x.no_parens()
    def str(self, mode, left_prec='bot', right_prec='bot', prec_order=global_prec_order):
      return '(' + self.x.str(mode, left_prec='bot', right_prec='bot', prec_order=prec_order) + ')'
  def make_transformer(constructors):
    class T(L.Transformer):
      def name(self, s): return Name(s[0].value)
      def var(self, s): return V(s[0])
      def parens(self, s): return Parens(s[0])
    for name, c in constructors.items():
      def go(name, c): # wrapper to get proper lexical scoping
        def transform(self, args):
          new_args = []
          fields = [v for _, v in c.__annotations__.items() if type(v) is not Str]
          # Each field of type F consumes two arguments: one for the name and one for the body
          i = 0
          for v in fields:
            if v is F:
              new_args.append(F(args[i], args[i+1]))
              i += 2
            else:
              new_args.append(args[i])
              i += 1
          return c(*new_args)
        setattr(T, name, transform)
      go(name, c)
    return T()
  productions = []
  constructors = {} # mapping from names of classes to themselves
  global parser_up_to_date
  # invariant: parser_up_to_date ==> the equalities below always hold
  grammar = make_fancy_grammar(global_prec_order, productions)
  parser = make_parser(grammar)
  transformer = make_transformer(constructors)
  class Parser:
    @staticmethod
    def add_production(p):
      global parser_up_to_date
      nonlocal productions, parser, transformer
      productions.append(p)
      constructors[classname_to_nt(p[0].__name__)] = p[0]
      parser_up_to_date = False
    @staticmethod
    def update_parser():
      global parser_up_to_date
      nonlocal parser, transformer
      if parser_up_to_date: return
      grammar = make_fancy_grammar(global_prec_order, productions)
      parser = make_parser(grammar)
      transformer = make_transformer(constructors)
      parser_up_to_date = True
    @staticmethod
    def parses(s):
      '''
      Returns the parses that stringify to s up to whitespace and extra parens.
      '''
      nonlocal parser, transformer
      Parser.update_parser()
      forest = parser.parse(s)
      parses = []
      seen = set()
      for tree in L.visitors.CollapseAmbiguities().transform(forest):
        # Sometimes forest does not share perfectly in highly ambiguous grammars, and there are duplicate trees
        if tree in seen: continue
        seen.add(tree)
        try: v = transformer.transform(tree)
        except: continue
        remove_whitespace = lambda s: ''.join(s.split())
        lhs = remove_whitespace(s)
        rhs = remove_whitespace(str(v))
        lhs_matches_rhs = lhs == rhs
        if lhs_matches_rhs:
          v = v.no_parens()
          parses.append(v)
      return parses
    @staticmethod
    def parse(s):
      '''
      Returns the unique parse yielded by parses(), if it exists.
      '''
      match Parser.parses(s):
        case []: raise ValueError(f'No parse for {s}')
        case [v]: return v
        case parses: raise ValueError(f"Ambiguous parse for {s}. Parses:\n{parses}")
    @staticmethod
    def current_grammar():
      nonlocal grammar
      Parser.update_parser()
      return grammar
  return Parser()
global_parser = make_parser()
del make_parser

def parse_mixfix(s):
  global global_parser

def mixfix(c):
  '''
  The decorator @mixfix allows declaring a binding-aware dataclass constructor
  that additionally supports mixfix precedence-based parsing and printing.
  
  For example, to declare And(p, q) that parses and pretty-prints as p + q:
    @mixfix
    class And:
      p: any
      plus: Str(' + ')
      q: any
  By default and when printing as str(), precedence mismatches are mediated by
  inserting parentheses using parens(). To change this behavior for other printing modes,
  one can specify a custom 'bracketer' using the optional field 'bracket', e.g.
    @mixfix
    class Add:
      p: any
      plus: Str(' + ')
      q: any
      bracket = lambda mode, s: f'\\left({s}\\right)' if mode == 'tex' else paren(s)
  to get LaTeX parentheses instead of the ordinary ones in mode 'tex'. It's not
  possible to change the bracketer used by str(), as that would break the parser.

  Precedences are declared as a partial ordering on 'cursor positions', which
  correspond to positions in the string produced by pretty-printing. Each field
  refers to the cursor position immediately after it in the pretty-printed
  string; the class name ('Add' in this case) is used to refer to the left-most
  cursor position. For example, visualizing the cursor position as |,
    Add        refers to   |p + q
    Add.p      refers to    p|+ q
    Add.plus   refers to    p +|q
    Add.q      refers to    p + q|
  The pretty-printer uses the partial ordering on cursor positions to decide
  which brackets can be omitted. It works as follows: each recursive call on
  subterm Add(x,y) additionally receives the names of the cursor positions to
  the left and right of Add(x,y) from the caller's perspective. (Initially,
  these names are 'bot', the bottom element of the partial ordering on cursor
  positions.) After pretty-printing Add(x,y) to a string, the names of the
  cursor positions to the left and right of Add(x,y) from Add's perspective (in
  this case Add and Add.q) are compared against the incoming cursor positions to
  decide whether or not brackets can be omitted. Specifically, if inner_l and
  inner_r denote the names of the cursor positions from Add's perspective, and
  incoming_l and incoming_r denote the names from the caller's perspective, then
  brackets can be omitted when
    inner_l >= incoming_l  and  inner_r >= incoming_r
  in the partial ordering of cursor positions.

  For example, the inequality Add >= Add.plus specifies right associativity: it
  allows the brackets in
    p + (q + r)
  to be omitted because the cursor position
    Add = |q + r
  has higher precedence than the cursor position
    Add.plus = p +|(q+r)
  Explicitly, at the recursive call on q+r, we have
    incoming_l = Add.plus
    incoming_r = Add.q
    inner_l = Add
    inner_r = Add.q
  and the brackets can be omitted because
    Add >= Add.plus  and  Add.q >= Add.q
  evaluates to True.

  Given a class declaration
    class C:
      x: tx
      y: Str(s)
      z: tz
      etc
  @mixfix generates a dataclass with
  - fields x: t, z: tz, ... (fields with 'string literal type' omitted)
  - class properties x, y, z, ... for referring to cursor positions denoted by these fields
  - class property __match_args__ = ('x', 'z', ...) for pattern matching against instances of C
  - method __repr__() that prints an instance of C for debugging
  - method str(m:str|None) that prints an instance of C in mode m.
  - method __str__(), like str() but prints specifically in mode None
  - method __eq__() that tests equality up to renaming of bound variables
  - method fresh(renaming) that freshens all bound variables (instances of the class F) in each field
  - method subst(**substitution) that applies the given substitution
  - method simple_names(renaming, in_use) that maximally simplifies disambiguators on bound variable names
  - method fvs() that produces the free variables of an instance of C
  - method no_parens() that removes Paren instances from subtrees
  '''
  name = c.__name__
  annotations = c.__annotations__
  assert len(annotations) != 0
  # Luckily, despite being a dict, c.__annotations__ contains items in declaration order,
  # so the order of the mixfix operators is preserved
  fields = tuple(k for k, v in annotations.items() if type(v) is not Str)
  def __init__(self, *args):
    assert len(fields) == len(args)
    for k, arg in zip(fields, args):
      setattr(self, k, arg)
  def __repr__(self):
    args = ','.join(repr(getattr(self, k)) for k in fields)
    return f'{name}({args})'
  def __eq__(self, other, renaming={}):
    return type(self) is type(other) and all(getattr(self, k).__eq__(getattr(other, k), renaming) for k in fields)
  def to_str(self, mode, left_prec='bot', right_prec='bot', prec_order=global_prec_order):
    def make_prec(field_name): return f'{name}.{field_name}' if field_name != name else name
    left_prec_inner = name
    right_prec_inner = make_prec(tuple(annotations.items())[-1][0]) # OK because annotations nonempty
    bracketing = not (prec_order.le(left_prec, left_prec_inner) and prec_order.le(right_prec, right_prec_inner))
    # (name of cursor position used to recur, corresponding field or None, string to append to output) for each entry in mixfix declaration
    precs = [('bot' if bracketing else name, None, '')] + list((make_prec(k), None if type(v) is Str else k, v) for (k, v) in annotations.items())
    if bracketing:
      precs[-1] = ('bot', precs[-1][1], precs[-1][2])
    # Compute left and right prec for each item
    items = (
      (l, (k, v), r)
      for (l, _, _), (r, k, v) in zip(precs, precs[1:])
    )
    res = ''
    for (left_prec_inner, (k, v), right_prec_inner) in items:
      if k is not None:
        res += getattr(self, k).str(mode, left_prec_inner, right_prec_inner, prec_order)
      else:
        assert type(v) is Str
        res += v.in_mode(mode)
    return self.__class__.bracket(mode, res) if bracketing else res
  def __str__(self): return self.str(None)
  def fresh(self, renaming={}):
    return self.__class__(*(getattr(self, k).fresh(renaming) for k in fields))
  def subst(self, substitution):
    return self.__class__(*(getattr(self, k).subst(substitution) for k in fields))
  def simple_names(self, renaming={}, in_use=None):
    if in_use is None: in_use = set(v for _, v in renaming.items())
    return self.__class__(*(getattr(self, k).simple_names(renaming, in_use) for k in fields))
  def fvs(self):
    return set(x for k in fields for x in getattr(self, k).fvs())
  def no_parens(self):
    return self.__class__(*(getattr(self, k).no_parens() for k in fields))
  c.__init__ = __init__
  c.__match_args__ = fields
  c.__repr__ = __repr__
  c.__eq__ = __eq__
  c.__str__ = __str__
  c.str = to_str
  c.fresh = fresh
  c.subst = subst
  c.simple_names = simple_names
  c.fvs = fvs
  c.no_parens = no_parens
  add_prec(c)
  def make_prec(k): return f'{name}.{k}'
  for k in annotations:
    prec_name = make_prec(k)
    setattr(c, k, prec_name)
    add_prec(prec_name)
  if not hasattr(c, 'bracket'):
    c.bracket = lambda mode, s: parens(s)
  global global_parser
  global_parser.add_production((c, [(make_prec(k), v if type(v) is not Str else v.s) for k, v in annotations.items()]))
  return c

# ---------- Examples ----------

if __name__ == '__main__':
  # Example 1: precedence-based printing for simple types
  #   t ::= 1 | t + t | t * t | t -> t
  # where 
  #   +, *, and -> are all right associative
  #   * takes precedence over +
  #   + and * take precedence to the left of ->
  #   (Usually, + and * also take precedence to the right of -> too, but leaving
  #   it out just to show you can)

  @mixfix
  class Top:
    s: Str('1')
  prec_top(Top)
  prec_top(Top.s)

  @mixfix
  class Times:
    p: any
    times: Str('*', pretty=' * ')
    q: any
  prec_ge(Times, Times.times) # right associative

  @mixfix
  class Plus:
    p: any
    plus: Str('+', pretty=' + ')
    q: any
  prec_ge(Plus, Plus.plus) # right associative
  prec_ges([(Times, Plus), (Times.q, Plus.p), (Times.q, Plus.q)]) # * takes precedence over +

  @mixfix
  class Pow:
    p: any
    to: Str('->', pretty=' -> ')
    q: any
  prec_ge(Pow, Pow.to) # right associative
  prec_ges([(Plus, Pow), (Plus.q, Pow.p)]) # + takes precedence on left of ->
  # Note: by transitivity, also get that * takes precedence on left of ->.

  def expect(want, have):
    if want != have:
      raise Exception(f'\nWant: {want}\nHave: {have}')
  def raises(thunk):
    try:
      v = thunk()
      raise ValueError(f'Instead of exception got {v}')
    except: pass

  # 1 requires no bracketing
  expect('1 * 1', Times(Top(), Top()).str('pretty'))
  # * is right-associative
  expect('1 * 1 * 1', Times(Top(), Times(Top(), Top())).str('pretty'))
  expect('(1 * 1) * 1', Times(Times(Top(), Top()), Top()).str('pretty'))
  # + is right-associative
  expect('1 + 1 + 1', Plus(Top(), Plus(Top(), Top())).str('pretty'))
  expect('(1 + 1) + 1', Plus(Plus(Top(), Top()), Top()).str('pretty'))
  # * takes precedence over +
  expect('1 * (1 + 1)', Times(Top(), Plus(Top(), Top())).str('pretty'))
  expect('(1 + 1) * 1', Times(Plus(Top(), Top()), Top()).str('pretty'))
  expect('1 + 1 * 1', Plus(Top(), Times(Top(), Top())).str('pretty'))
  expect('1 * 1 + 1', Plus(Times(Top(), Top()), Top()).str('pretty'))
  # -> is right-associative
  expect('1 -> 1 -> 1', Pow(Top(), Pow(Top(), Top())).str('pretty'))
  expect('(1 -> 1) -> 1', Pow(Pow(Top(), Top()), Top()).str('pretty'))
  # * and + take precedence over -> on left
  expect('1 * 1 -> 1', Pow(Times(Top(), Top()), Top()).str('pretty'))
  expect('1 * (1 -> 1)', Times(Top(), Pow(Top(), Top())).str('pretty'))
  expect('1 + 1 -> 1', Pow(Plus(Top(), Top()), Top()).str('pretty'))
  expect('1 + (1 -> 1)', Plus(Top(), Pow(Top(), Top())).str('pretty'))
  # * and + do NOT take precedence over -> on right
  expect('1 -> (1 * 1)', Pow(Top(), Times(Top(), Top())).str('pretty'))
  expect('1 -> (1 + 1)', Pow(Top(), Plus(Top(), Top())).str('pretty'))

  # Thanks to precedences, the following strings parse unambiguously
  expect(Plus(Top(), Top()), global_parser.parse('1 + 1'))
  expect(Plus(Top(), Plus(Top(), Top())), global_parser.parse('1 + 1 + 1'))
  expect(Plus(Plus(Top(), Top()), Top()), global_parser.parse('(1 + 1) + 1'))
  expect(Plus(Times(Top(), Top()), Top()), global_parser.parse('1 * 1 + 1'))
  expect(Plus(Pow(Top(), Top()), Top()), global_parser.parse('(1 -> 1) + 1'))
  expect(Times(Top(), Times(Top(), Top())), global_parser.parse('1 * 1 * 1'))
  expect(Pow(Top(), Pow(Top(), Top())), global_parser.parse('1 -> 1 -> 1'))

  # * and + need parens to right of ->
  raises(lambda: global_parser.parse('1 -> 1 + 1'))
  raises(lambda: global_parser.parse('1 -> 1 * 1'))

  # Superfluous parentheses are allowed
  expect(Plus(Top(), Plus(Top(), Top())), global_parser.parse('1 + (1 + 1)'))
  expect(Plus(Plus(Top(), Top()), Top()), global_parser.parse('((1 + 1) + 1)'))
  expect(Plus(Plus(Top(), Top()), Top()), global_parser.parse('(((1 + 1)) + (1))'))

  # Spaces are flexible, even though pretty-printing produces canonical spacing
  expect(Plus(Top(), Plus(Top(), Top())), global_parser.parse('1+1+1'))
  expect(Plus(Times(Top(), Top()), Top()), global_parser.parse('1*1+1'))
  expect(Plus(Times(Top(), Top()), Top()), global_parser.parse('1  *1+     1'))

  # Example 2: extending the language with quantifiers

  @mixfix
  class Forall:
    forall: Str('forall ', pretty='∀ ')
    xp: F
  @mixfix
  class Exists:
    forall: Str('exists ', pretty='∃ ')
    xp: F
  prec_ges([(Forall.xp, Exists.xp), (Exists.xp, Forall.xp)])
  @mixfix
  class Eq:
    m: any
    eq: Str('=', pretty=' = ')
    n: any
  prec_ge(Eq.n, Exists.xp) # by transitivity, Eq.n >= Forall.xp
  prec_ge(Times.q, Exists.xp)

  p = Forall(F('x', lambda x: Exists(F('y', lambda y: Eq(x, y)))))
  expect('∀ x@0. ∃ y@1. x@0 = y@1', p.str('pretty'))
  expect('∀ x. ∃ y. x = y', p.simple_names().str('pretty'))

  # Equality up to renaming
  mxy = Forall(F('x', lambda x: Forall(F('y', lambda y: Eq(x, y)))))
  muv = Forall(F('u', lambda u: Forall(F('v', lambda v: Eq(u, v)))))
  muv_flip = Forall(F('u', lambda u: Forall(F('v', lambda v: Eq(v, u)))))
  expect(True, mxy == muv)
  expect(False, mxy == muv_flip)

  # Parsing of C identifiers as variable names
  expect(V(Name('a')), global_parser.parse('a'))
  expect(V(Name('snake_case123')), global_parser.parse('snake_case123'))
  expect(V(Name('_abc')), global_parser.parse('_abc'))

  # Parsing of quantified formulas
  # Note: tests are happening up to renaming of bound variables, because
  # F.__eq__ works up to renaming
  expect(Forall(F('x', lambda x: x)), global_parser.parse('forall x. x'))
  expect(Exists(F('x', lambda x: x)), global_parser.parse('exists x. x'))
  expect(Forall(F('p', lambda p: Times(p, p))), global_parser.parse('forall x. x * x'))
  expect(Forall(F('x', lambda x: Exists(F('y', lambda y: Eq(x, y))))), global_parser.parse('forall x. exists y. x = y'))
  expect(
    Forall(F('x', lambda x: Forall(F('y', lambda y: Exists(F('z', lambda z: Times(Eq(y, y), Eq(x, y)))))))), 
    global_parser.parse('forall x. forall y. exists z. (y = y) * (x = y)')
  )
  raises(lambda: global_parser.parse('forall x. forall y. exists z. (y = y) * x = y')) # missing parens around x = y

  # Example 3: pattern matching on ABTs

  def simplify(p):
    match p:
      case Eq(m, n): return Top() if m == n else Eq(simplify(m), simplify(n))
      case V(x): return V(x)
      case Forall(F([x, p])):
        p = simplify(p)
        if x not in p.fvs(): return p
        else: return Forall(F(x, p))
      case Exists(F([x, p])):
        p = simplify(p)
        if x not in p.fvs(): return p
        else: return Exists(F(x, p))
      case Plus(p, q): return Plus(simplify(p), simplify(q))
      case Times(p, q):
        match simplify(p), simplify(q):
          case Top(), Top(): return Top()
          case Top(), q: return q
          case p, Top(): return p
          case p, q: return Times(p, q)
      case Pow(p, q): return Pow(simplify(p), simplify(q))
      case _:
        assert False

  p = Forall(F('x', lambda x: Forall(F('y', lambda y: Exists(F('z', lambda z: Times(Eq(y, y), Times(Eq(x, y), Eq(z, z)))))))))
  expect(set(), p.fvs())
  expect('∀ x. ∀ y. ∃ z. (y = y) * (x = y) * (z = z)', p.simple_names().str('pretty'))
  p = simplify(p)
  expect('∀ x. ∀ y. x = y', p.simple_names().str('pretty'))

  # Example 4: untyped LC

  @mixfix
  class Lam:
    lam: Str('\\', pretty='λ')
    m: F
  @mixfix
  class App:
    m: any
    app: Str(' ')
    n: any
  prec_ge(App.n, App.m) # left-associative
  prec_ge(App.n, Lam.m) # application binds stronger than λ

  # str uses \ and condensed . while pretty uses λ
  id = Lam(F('x', lambda x: x))
  expect('λx. x', id.simple_names().str('pretty'))
  expect(r'\x.x', str(id.simple_names()))

  # Check printing of function applications
  expect('(λx. x) ((λx. x) (λx. x))', App(id, App(id, id)).simple_names().str('pretty'))
  expect('(λx. x) (λx. x) (λx. x)', App(App(id, id), id).simple_names().str('pretty'))

  # One-step reduction
  class Stuck(Exception): pass
  def step(m):
    match m:
      case Lam(F([x, m])): return Lam(F(x, step(m)))
      case App(Lam(F([x, m])), n): return m.subst({x: n})
      case App(m, n):
        try: return App(step(m), n)
        except Stuck: return App(m, step(n))
      case V(x): raise Stuck()

  expect('λx. x', step(App(id, id)).simple_names().str('pretty'))

  # Check capture-avoiding substitution on \y. (\x. \y. x) y
  k = lambda y: Lam(F('x', lambda x: Lam(F('y', lambda y: x))))
  v = lambda y: y
  m = Lam(F('y', lambda y: App(k(y), v(y))))
  expect('λy. (λx. λy@0. x) y', m.simple_names().str('pretty'))
  m = step(m)
  expect('λy. λy@0. y', m.simple_names().str('pretty'))

  # Omega Omega -> Omega Omega
  omega = Lam(F('x', lambda x: App(x, x)))
  expect('λx. x x', omega.simple_names().str('pretty'))
  omega2 = App(omega, omega)
  expect('(λx. x x) (λx. x x)', omega2.simple_names().str('pretty'))
  omega2 = step(omega2)
  expect('(λx. x x) (λx. x x)', omega2.simple_names().str('pretty'))

  # Parsing
  expect(omega, global_parser.parse(r'\x. x x'))
  expect(omega, global_parser.parse(r'\x. (x x)'))
  expect(omega2, global_parser.parse(r'(\x. (x x)) ((\x. (x x)))'))
  expect(App(App(id, id), id), global_parser.parse(r'(\x.x) (\x.x) (\x.x)'))
  # Even though the production for App is term -> term term, this still has a
  # unique parse because parsing of identifiers always takes the longest match
  expect(V(Name('xy')), global_parser.parse(r'xy'))

  # Recognizes the outer parens as superfluous and spaces unnecessary
  expect(
    Lam(F('f', lambda f: App(Lam(F('x', lambda x: x)), f))),
    global_parser.parse(r'(\f.(\x.x) f)')
  )

  # Some longer parses (used to lead to exponential blowup; now fine because
  # parsing of F is hard-coded to expect a name in binding position)
  y = Lam(F('f', lambda f: App(
    Lam(F('x', lambda x: App(f, App(x, x)))),
    Lam(F('x', lambda x: App(f, App(x, x)))))
  ))
  snd_y = App(Lam(F('y', lambda y: Lam(F('p', lambda p: p)))), y)
  is_zero = Lam(F('n', lambda n: App(
    App(n, Lam(F('t', lambda t: Lam(F('f', lambda f: t))))),
    Lam(F('n', lambda n: Lam(F('t', lambda t: Lam(F('f', lambda f: f)))))))
  ))
  expect(snd_y, global_parser.parse(r'(\y.\p.p) (\f.(\x.f (x x)) (\x.f (x x)))'))
  expect(
    App(snd_y, is_zero),
    global_parser.parse(r'(\y.\p.p) (\f.(\x.f (x x)) (\x.f (x x))) (\n.n (\t.\f.t) (\n.\t.\f.f))')
  )

  # Really long input that can't be parsed efficiently without good grammar generation
  global_parser.parse(r'(\Y.\iszero.\add.\z.\s.\cons.\fst.\snd.(\pred.(\tri. tri (s (s (s z)))) (Y (\tri.\n.iszero n z (add n (tri (pred n)))))) (\n.fst (n (\p. cons (snd p) (s (snd p))) (cons z z)))) (\f.(\x.(f (x x))) (\x.(f (x x)))) (\n.n (\n.\t.\f.f) (\t.\f.t)) (\m.\n.\s.\z.m s (n s z)) (\s.\z.z) (\n.\s.\z.s (n s z)) (\x.\y.\f.f x y) (\p.p (\x.\y.x)) (\p.p (\x.\y.y))')
