from util import expect, raises

import lark as L
import networkx as N
from dataclasses import dataclass

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
def prec_bot(p):
  global_prec_order.add_bot(to_prec(p))
  parser_up_to_date = False
def prec_top(p):
  global_prec_order.add_top(to_prec(p))
  parser_up_to_date = False

def prec_ges(pqs):
  for p, q in pqs:
    prec_ge(p, q)
def prec_pairwise_ge(ps, qs):
  for p in ps:
    for q in qs:
      prec_ge(p, q)

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
  def __str__(self): return self.x if self.n is None else f'{self.x}_{{{self.n}}}'
  def fresh(self): return Name(self.x, next(global_nats))
  def with_n(self, n): return Name(self.x, n)

# Syntax trees are built from F (defined below) and classes that inherit from Term.
# Term allows pattern matching against terms in general and recursively manipulating their children.
class Term:
  __match_args__ = ('head_constructor', 'children',)
  head_constructor = property(lambda self: self.__class__)
  def get_children(self): return [getattr(self, x) for x in self.__class__.__match_args__]
  def set_children(self, new):
    for k, v in zip(self.__class__.__match_args__, new):
      setattr(self, k, v)
  children = property(get_children, set_children)

class V(Term):
  '''
  An occurrence of a variable name.
  Usually not used to construct variables explicitly; see help(F).
  '''
  __match_args__ = ('x',)
  def __init__(self, x): self.x = x
  def __eq__(self, other, renaming={}): return type(other) is V and (renaming[self.x] == other.x if self.x in renaming else self.x == other.x)
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
  - F('x', lambda x, ...: e[x, ...]) represents a term e with free variables x, ...
    Constructs a value F(Name('x', n), ..., e[V(Name('x', n)), ...]) with n, ... fresh.
  - F(x:Name, ..., e) represents a term e with free variables x, ...
    Does not do any freshening.
  Pattern matching against an instance of F produces [x:Name, ..., e:term] with x fresh.
  Therefore, while F instances are constructed by F('x', ..., lambda x, ...: e) and F(x, ..., e),
  they are pattern-matched against as F([x, ..., e]). This is to ensure that the
  fresh name and its body are extracted together. To support pattern F(x, ..., e) would
  require different getters for the names and the body. Depending on the order
  in which the getters are called during pattern matching, this could cause e to
  be scoped with respect to a stale version of x, ...
  '''
  __match_args__ = ('unwrap',)
  def __init__(self, *args):
    *xs, e = args
    assert len(xs) > 0
    assert len(set(xs)) == len(xs)
    if type(xs[0]) is str and type(e) is type(lambda x: x):
      self.xs = [Name(x).fresh() for x in xs]
      self.e = e(*map(V, self.xs))
    elif type(xs[0]) is Name:
      self.xs = xs
      self.e = e
    else:
      raise ValueError(f'F({repr(xs)}, {repr(e)})')

  def __repr__(self):
    return f'F({repr(self.xs)}, {repr(self.e)})'
  
  def __eq__(self, other, renaming={}):
    return type(other) is F and len(self.xs) == len(other.xs) and self.e.__eq__(other.e, renaming | {x: y for x, y in zip(self.xs, other.xs)})

  def __str__(self): return self.str(None)

  def fresh(self, renaming={}):
    xs = [x.fresh() for x in self.xs]
    e = self.e.fresh(renaming | {old: new for old, new in zip(self.xs, xs)})
    return F(*xs, e)

  def subst(self, substitution):
    xs = [x.fresh() for x in self.xs]
    e = self.e.subst(substitution | {old: V(new) for old, new in zip(self.xs, xs)})
    return F(*xs, e)

  def simple_names(self, renaming={}, in_use=None):
    if in_use is None: in_use = set(v for _, v in renaming.items())
    banned = in_use | self.fvs()
    xs = []
    for old_x in self.xs:
      new_x = (
        old_x.with_n(None) if old_x.with_n(None) not in banned else
        next(old_x.with_n(n) for n in nats() if old_x.with_n(n) not in banned)
      )
      xs.append(new_x)
      banned.add(new_x)
    e = self.e.simple_names(renaming | {old: new for old, new in zip(self.xs, xs)}, in_use | set(xs))
    return F(*xs, e)

  def fvs(self):
    return self.e.fvs() - set(self.xs)

  def no_parens(self): return F(*self.xs, self.e.no_parens())

  def get_unwrap(self):
    e = self.fresh()
    return [*e.xs, e.e]
  unwrap = property(get_unwrap)

  def str(self, mode, left_prec='bot', right_prec='bot', prec_order=global_prec_order):
    dot = '.' if mode is None else '. '
    binders = ' '.join(str(x) for x in self.xs)
    return f"{binders}{dot}{self.e.str(mode, left_prec='bot', right_prec=right_prec, prec_order=prec_order)}"


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

# Parser of grammar updated by each invocation of @mixfix.
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
      names : CNAMES
      CNAMES : CNAME (WS CNAME)*
  
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
    #   c : p_r some_string t_q for each production c at prec p with subprecs [r, q]
    #
    #   ?bot_bot : p_q for each successor (p,q) of (bot,bot) in poset
    #   ?p_q : c for each production with left- and right-precs p and q
    #       | p'_q' for each successor (p',q') of (p,q) in poset
    #   ...
    #   ?top_top : atom | other top_top productions
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
    #   There is probably a more efficient way.
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
    productions = {} # maps strings of the form str_of_lr(l, r) to a list of strings encoding productions
    constructor_productions = {} # maps constructor names to their productions
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
        name = classname_to_nt(c.__name__)
        productions[str_lr].append(name)
        pieces = []
        for (new_l, _), (new_r, v) in zip([(to_prec(c), None)] + p, p):
          if type(v) is str:
            escape = lambda s: f'"{repr(s)[1:-1]}"'
            if v != '': pieces.append(escape(v))
          elif v is F:
            new_lr = make_lr('bot', new_r)
            pieces.append('names')
            pieces.append('"."')
            pieces.append(str_of_lr(new_lr))
            go(new_lr)
          else:
            new_lr = make_lr(new_l, new_r)
            pieces.append(str_of_lr(new_lr))
            go(new_lr)
        assert name not in constructor_productions # each constructor should correspont to a unique lr pair
        constructor_productions[name] = ' '.join(pieces)
      for next_lr in prec_graph.successors(lr):
        productions[str_lr].append(str_of_lr(canon_lr[next_lr]))
        go(next_lr)
    go(bot_lr)
    str_productions = '\n\n'.join(
      f'      ?{k} : ' + '\n      | '.join(p)
      for k, p in productions.items()
    )
    str_constructor_productions = '\n'.join(
      f'      {k} : {p}'
      for k, p in constructor_productions.items()
    )
    return f'''{str_productions}\n\n{str_constructor_productions}

      ?atom : name -> var
      | "(" term ")" -> parens

      name : CNAME
      names : CNAMES
      CNAMES : CNAME (WS CNAME)*

      %import common.CNAME
      %import common.ESCAPED_STRING
      %import common.SIGNED_NUMBER
      %import common.WS
      %ignore WS
    '''
  def make_parser(grammar):
    return L.Lark(grammar, start='term', ambiguity='forest')
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
      def names(self, s): return [Name(x) for x in s[0].value.split()]
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
              new_args.append(F(*args[i], args[i+1]))
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
  def parse_forest_to_parse_trees(forest, stats):
    # The grammar produced by make_fancy_grammar() seems to guarantee
    # shared packed parse forests (SPPFs) linear in input length for reasonable
    # posets. However, transforming these SPPFs into trees leads to an
    # exponential blowup: a simple example is that strings
    #   (a1) .. (an)
    # may have parse count exponential in n. This occurs when there are multiple
    # incomparable ways to get to top_top. In such a situation the generated
    # grammar looks something like
    #   bot_bot : a | b
    #   a : ... | top_top
    #   b : ... | top_top
    #   top_top : "(" bot_bot ")" | ...
    # and now there is a reduce-reduce conflict at EOF because it's unclear
    # whether a top_top should be reduced to an instance of a or b. So for each
    # (ai) in the example above there are two options, causing the exponential
    # blowup. To see this more clearly print the grammars generated by Example 1
    # in the test cases below. This blowup is removable: the SPPF will have
    # nodes that share the result of parsing the top_top, and those nodes are
    # irrelevant to the construction of the parse tree, so a post-pass can
    # remove those nodes and yield a tree with no blowup. So the strategy for
    # getting from SPPF to parse tree is as follows:
    # - contract() and coalesce() remove the above-mentioned sources of blowup
    #   from the SPPF.
    # - TreeForestTransformer is used to turn the (now hopefully linear) SPPF
    #   into a parse tree with _ambig nodes.
    # - Since we are now working with the SPPF and parse tree manually, we have
    #   to use a Transformer to manually filter out string literals from the
    #   parse tree.
    #
    # I couldn't figure out how to make lark's SPPF visitors do the linear time
    # simplification of the graph in a nice way, so for now contract() and
    # coalesce() convert the forest into an explicit, easier-to-traverse graph
    # and do the transformations on that.
    @dataclass
    class ASymbolNode:
      s: any
      start: any
      end: any
      children: list[int]
    @dataclass
    class APackedNode:
      s: any
      rule: any
      start: any
      children: list[int]
    @dataclass
    class ATokenNode:
      node: any
    def graph_of(node):
      '''
      Convert an SPPF into a rooted graph (graph, root).
      Vertices are represented as id()s and graph maps vertices to the Node
      dataclasses defined above.
      '''
      from lark.parsers.earley_forest import TokenNode
      graph = {}
      def go_symbol_node(node):
        nonlocal graph
        if id(node) in graph: return
        if isinstance(node, TokenNode):
          graph[id(node)] = ATokenNode(node)
        else:
          graph[id(node)] = ASymbolNode(node.s, node.start, node.end, [id(c) for c in node.children])
          for c in node.children:
            go_packed_node(c)
      def go_packed_node(node):
        nonlocal graph
        if id(node) in graph: return
        graph[id(node)] = APackedNode(node.s, node.rule, node.start, [id(c) for c in [node.left, node.right] if c is not None])
        if node.left is not None: go_symbol_node(node.left)
        if node.right is not None: go_symbol_node(node.right)
      go_symbol_node(node)
      return (graph, id(node))
    def forest_of(graph, root):
      '''Convert a rooted graph (graph, root) back into an SPPF.'''
      from lark.parsers.earley_forest import SymbolNode, PackedNode
      forest = {}
      def go(v, parent):
        nonlocal forest, graph
        if v in forest: return forest[v]
        match graph[v]:
          case ASymbolNode(s, start, end, children):
            s = SymbolNode(s, start, end)
            forest[v] = s
            children = [go(c, s) for c in children]
            for c in children:
              s.add_family(c.s, c.rule, c.start, c.left, c.right)
            return s
          case APackedNode(s, rule, start, children):
            assert parent is not None
            children = [go(c, None) for c in children]
            match children:
              case [p]: return PackedNode(parent, s, rule, start, None, p)
              case [p, q]: return PackedNode(parent, s, rule, start, p, q)
              case _: assert False
          case ATokenNode(node): return node
      return go(root, None)
    def contract_step(graph, root):
      '''Inline applications of ?term_* nonterminals with one child.'''
      visited = set()
      parents = {}
      for v, node in graph.items():
        match node:
          case APackedNode(_, _, _, children):
            for i, c in enumerate(children):
              if c not in parents: parents[c] = set()
              parents[c].add((v, i))
      def go(v):
        if v in visited: return
        visited.add(v)
        def join(children):
          for c in children:
            go(c)
        match graph[v]:
          case ASymbolNode(s, _, _, [w]) if hasattr(s, 'name') and s.name.startswith('term'):
            match graph[w]:
              case APackedNode(_, _, _, [c]) if v in parents:
                for p, i in parents[v]:
                  graph[p].children[i] = c
                parents[c] = parents[v]
                go(c)
              case _: join([w])
          case ASymbolNode(_, _, _, children): 
            join(children)
          case APackedNode(_, _, _, children):
            for c in children:
              go(c)
          case ATokenNode(_): return
      return go(root)
    def gc(graph, root):
      '''
      Remove vertices in graph not reachable from root and return whether any
      change occured.
      '''
      marked = set()
      def go(v):
        nonlocal marked
        if v in marked: return
        marked.add(v)
        match graph[v]:
          case ASymbolNode(_, _, _, children):
            for c in children: go(c)
          case APackedNode(_, _, _, children):
            for c in children: go(c)
          case ATokenNode(_): pass
      go(root)
      changed = False
      for v in tuple(v for v in graph):
        if v not in marked:
          del graph[v]
          changed = True
      return changed
    def contract(graph, root, stats):
      '''Iterate contract_step to a fixed point.'''
      stats.contract_steps = -1
      while True:
        contract_step(graph, root)
        stats.contract_steps += 1
        changed = gc(graph, root)
        if not changed: return
    def coalesce_step(graph, root):
      '''
      Ambiguous nodes may have inlinable ?term_* children that point to the same subgraph.
      Remove the redundant children.
      '''
      visited = set()
      def go(v):
        if v in visited: return
        visited.add(v)
        match graph[v]:
          case ASymbolNode(s, _, _, children) if hasattr(s, 'name') and s.name.startswith('term'):
            term_cases = set()
            new_children = []
            for w in children:
              match graph[w]:
                case APackedNode(_, _, _, [c]):
                  if c in term_cases: continue
                  term_cases.add(c)
                  new_children.append(w)
                case _:
                  new_children.append(w)
            graph[v].children = new_children
            for c in new_children: go(c)
          case ASymbolNode(_, _, _, children):
            for w in children: go(w)
          case APackedNode(_, _, _, children):
            for w in children: go(w)
          case ATokenNode(_): return
      return go(root)
    def coalesce(graph, root, stats):
      '''Iterate coalesce to a fixed point.'''
      stats.coalesce_steps = -1
      while True:
        stats.coalesce_steps += 1
        coalesce_step(graph, root)
        changed = gc(graph, root)
        if not changed: return
    def parse_tree(f):
      '''Convert a SPPF into a (possibly-ambiguous) parse tree.'''
      from lark.parsers.earley_forest import TreeForestTransformer
      return TreeForestTransformer(resolve_ambiguity=False).transform(f)
    def strip_tokens(f):
      '''Manually filter tokens out of the a parse tree.'''
      from lark import Transformer, Tree, Token
      class T(Transformer):
        def name(self, data): return Tree('name', data)
        def names(self, data): return Tree('names', data)
        def var(self, data): return Tree('var', data)
        def string(self, data): return Tree('string', data)
        def number(self, data): return Tree('number', data)
        def parens(self, data): return Tree('parens', [data[1]])
        def __default__(self, data, children, meta):
          if data == 'term' or data.startswith('term_') and len(children) == 1: return children[0]
          elif data in constructors:
            return Tree(data, [c for c in children if type(c) is not Token])
          else: return Tree(data, children)
      return T().transform(f)
    g, root = graph_of(forest)
    contract(g, root, stats)
    coalesce(g, root, stats)
    forest = forest_of(g, root)
    tree = parse_tree(forest)
    tree = strip_tokens(tree)
    return L.visitors.CollapseAmbiguities().transform(tree)
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
      nonlocal grammar, productions, parser, transformer
      if parser_up_to_date: return
      grammar = make_fancy_grammar(global_prec_order, productions)
      parser = make_parser(grammar)
      transformer = make_transformer(constructors)
      parser_up_to_date = True
    @staticmethod
    def parses(s, with_stats=False):
      '''
      Returns the parses that stringify to s up to whitespace and extra parens.
      If with_stats=True, additionally return an object containing the following
      statistics measuring how bad the parse was:
        .contract_steps = number of calls to contract_step that did work
        .coalesce_steps = number of calls to coalesce_step that did work
        .trees = number of parse trees considered
        .duplicates = number of duplicate parse trees
          (Sometimes inlining ?term_ nonterminals produces duplicates)
      '''
      nonlocal parser, transformer
      Parser.update_parser()
      forest = parser.parse(s)
      parses = []
      seen = set()
      @dataclass
      class Stats:
        contract_steps: int = 0
        coalesce_steps: int = 0
        trees: int = 0
        duplicates: int = 0
      stats = Stats()
      if s == '(((1 + 1)) + (1))':
        pass
      for tree in parse_forest_to_parse_trees(forest, stats):
        stats.trees += 1
        if tree in seen:
          stats.duplicates += 1
          continue
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
      if with_stats: return parses, stats
      else: return parses
    @staticmethod
    def parse(s, with_stats=False):
      '''
      Returns the unique parse yielded by parses(), if it exists.
      '''
      if with_stats:
        parses, stats = Parser.parses(s, with_stats=True)
      else:
        parses = Parser.parses(s, with_stats=False)
      match parses:
        case []: raise ValueError(f'No parse for {s}')
        case [v]: return (v, stats) if with_stats else v
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

def s(s, with_stats=False): return global_parser.parse(s, with_stats=with_stats)

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
  class Top(Term):
    s: Str('1')
  prec_top(Top)
  prec_top(Top.s)

  @mixfix
  class Times(Term):
    p: any
    times: Str('*', pretty=' * ')
    q: any
  prec_ge(Times, Times.times) # right associative

  @mixfix
  class Plus(Term):
    p: any
    plus: Str('+', pretty=' + ')
    q: any
  prec_ge(Plus, Plus.plus) # right associative
  prec_ges([(Times, Plus), (Times.q, Plus.p), (Times.q, Plus.q)]) # * takes precedence over +

  @mixfix
  class Pow(Term):
    p: any
    to: Str('->', pretty=' -> ')
    q: any
  prec_ge(Pow, Pow.to) # right associative
  prec_ges([(Plus, Pow), (Plus.q, Pow.p)]) # + takes precedence on left of ->
  # Note: by transitivity, also get that * takes precedence on left of ->.

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