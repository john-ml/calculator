DEBUG = False
debug = print if DEBUG else (lambda *xs: None)

# ---------- Mixfix printing ----------

def parens(s): return f'\\left({s}\\right)'

# Global poset on cursor positions used by pretty-printer (see help(mixfix))
from poset import Poset
global_prec_order = Poset().add_bot('bot').add_top('top')
def to_prec(p): return p.__name__ if type(p) is type else p
def prec_ge(p, q): global_prec_order.add(to_prec(q), to_prec(p))
def prec_ges(pqs):
  for p, q in pqs:
    prec_ge(p, q)
def prec_bot(p): global_prec_order.add_bot(to_prec(p))
def prec_top(p): global_prec_order.add_top(to_prec(p))

class Str:
  r'''
  Helper class used to specify string literals in mixfix declarations.
  S(s) specifies the string literal s is to be used in both parsing and
  pretty-printing.  Optionally, one can specify a different string literal t to
  be used during parsing (e.g. to parse \x.e as a lambda term and pretty-print
  it in LaTeX with \lambda) by S(s, parse=t) or S(s, t).

  For example use of S see help(mixfix).
  '''
  def __init__(self, pretty, parse=None):
    self.pretty = pretty
    self.parse = pretty if parse is None else parse

# Parser of highly ambiguous grammar updated by each invocation of @mixfix.
def make_parser():
  import lark as L
  # Annoyingly, lark nonterminals must contain only lowercase letters.
  # So munge class names to fit this format. Assumes no class names contain _
  def classname_to_nt(s): return 'c' + ''.join('_' + c.lower() if c.isupper() else c for c in s)
  def nt_to_classname(s): return ''.join('' if c == '_' else c.upper() if prev == '_' else c for (prev, c) in zip(s[1:], s[2:]))
  # The grammar is stored as a list of productions on a single nonterminal
  # 'term'. A production like
  #   term -> term + term
  # for a mixfix constructor C is represented as the tuple
  #   (C, [None, "+", None])
  def make_grammar(ps):
    # TODO could construct the grammar more intelligently using the precedence
    # poset so there are fewer ambiguities to deal with
    escape = lambda s: f'"{repr(s)[1:-1]}"'
    lines = ''.join(
      f'\n      | {" ".join("term" if s is None else escape(s) for s in p)} -> {classname_to_nt(c.__name__)}' for c, p in ps
    )
    return f'''
      ?term : atom{lines}
      | "(" term ")"
  
      ?atom : CNAME -> identifier
      | ESCAPED_STRING -> string
      | SIGNED_NUMBER -> number
  
      %import common.CNAME
      %import common.ESCAPED_STRING
      %import common.SIGNED_NUMBER
      %import common.WS
      %ignore WS
    '''
  def make_parser(ps):
    debug('making grammar')
    debug(make_grammar(ps))
    return L.Lark(make_grammar(ps), start='term', ambiguity='explicit')
  def make_transformer(constructors):
    debug('making transformer', constructors)
    class T(L.Transformer):
      def identifier(self, s):
        return V(Name(s[0].value))
    for name, c in constructors.items():
      def go(name, c): # wrapper to get proper lexical scoping
        def transform(self, args):
          return c.transform(args) if hasattr(c, 'transform') else c(*args)
        setattr(T, name, transform)
      go(name, c)
    return T()
  productions = []
  constructors = {} # mapping from names of classes to themselves
  # invariant: the 2 equalities below always hold
  parser = make_parser(productions)
  transformer = make_transformer(constructors)
  class Parser:
    @staticmethod
    def add_production(p):
      nonlocal productions, parser, transformer
      debug('adding production', p)
      productions.append(p)
      parser = make_parser(productions)
      constructors[classname_to_nt(p[0].__name__)] = p[0]
      transformer = make_transformer(constructors)
    @staticmethod
    def parses(s):
      '''
      Returns the parses that pretty-print as s up to whitespace and extra parens.
      '''
      nonlocal parser, transformer
      forest = parser.parse(s)
      # Condense all long strings of spaces into a single space
      def condense(s):
        while True:
          new = s.replace('  ', ' ')
          if s == new: return s
          s = new
      # Check if t is a version of s with extraneous parens removed
      def reducible_to(s, t):
        if s == t: return True
        set_s = set(s)
        set_t = set(t)
        if set_s.symmetric_difference(set_t) - set('()') != set(): return False
        if (set_s - set_t) - set('()') != set(): return False
        i = 0
        j = 0
        while True:
          if j == len(t):
            return True
          elif s[i] == t[j]:
            i += 1
            j += 1
          elif s[i] in '()':
            i += 1
          else:
            return False
      parses = []
      for tree in L.visitors.CollapseAmbiguities().transform(forest):
        debug('trying tree', tree)
        debug('constructors', constructors)
        try: v = transformer.transform(tree)
        except: continue
        lhs = condense(s)
        rhs = condense(str(v))
        b = reducible_to(lhs, rhs)
        debug(f'reducible_to({lhs}, {rhs}) = {b}')
        if b:
          parses.append(v)
      return parses
    @staticmethod
    def parse(s):
      '''
      Return the unique parse that pretty-prints as s up to whitespace and extra
      parens, if it exists.
      '''
      match Parser.parses(s):
        case []: raise ValueError(f'No parse for {s}')
        case [v]: return v
        case parses: raise ValueError(f"Ambiguous parse for {s}. Parses:\n{parses}")
    @staticmethod
    def current_grammar():
      nonlocal productions
      return make_grammar(productions)
  return Parser()
global_parser = make_parser()
del make_parser

def parse_mixfix(s):
  global global_parser

def mixfix(c):
  '''
  The decorator @mixfix allows declaring dataclass that additionally support
  mixfix precedence-based parsing and pretty-printing.
  
  For example, to declare an operator And(p, q) that pretty-prints as p + q:
    @mixfix
    class And:
      p: any
      plus: Str(' + ')
      q: any
  By default, precedence mismatches are mediated by inserting parentheses using
  parens(), but one can specify a different 'bracketer' using the optional field
  'bracket', e.g.
    @mixfix
    class Add:
      p: any
      plus: Str(' + ')
      q: any
      bracket = lambda s: f'({s})'
  to get ordinary parentheses instead of the LaTeX ones.

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
  inner_r denote the names of the cursor positions from F's perspective, and
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
  Generates a dataclass with
  - fields x: t, z: tz, ... (fields with 'string literal type' omitted)
  - method fresh(renaming) that freshens all bound variables (instances of the class F) in each field
  - method subst(**substitution) that applies the given substitution
  - method simple_names(renaming, in_use) that maximally simplifies disambiguators on bound variable names
  - method fvs() that produces the free variables of an instance of C
  - method pretty() that pretty-prints an instance of C, omitting brackets as allowed by the global precedence order
  - method __repr__() that prints an instance of C for debugging
  - method __str__() that calls pretty()
  - method __eq__() that tests equality up to renaming of bound variables
  - class properties x, y, z, ... for referring to cursor positions denoted by these fields
  - class property __match_args__ = ('x', 'z', ...) for pattern matching against instances of C
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
  def fresh(self, renaming):
    return self.__class__(*(getattr(self, k).fresh(renaming) for k in fields))
  def subst(self, substitution):
    return self.__class__(*(getattr(self, k).subst(substitution) for k in fields))
  def simple_names(self, renaming={}, in_use=set()):
    return self.__class__(*(getattr(self, k).simple_names(renaming, in_use) for k in fields))
  def fvs(self):
    debug(self, [(getattr(self, k), type(getattr(self, k))) for k in fields])
    return set(x for k in fields for x in getattr(self, k).fvs())
  def __repr__(self):
    args = ','.join(repr(getattr(self, k)) for k in fields)
    return f'{name}({args})'
  def __eq__(self, other, renaming={}):
    return type(self) is type(other) and all(getattr(self, k).__eq__(getattr(other, k), renaming) for k in fields)
  def pretty(self, left_prec='bot', right_prec='bot', prec_order=global_prec_order):
    def make_prec(field_name): return f'{name}.{field_name}' if field_name != name else name
    left_prec_inner = name
    right_prec_inner = make_prec(tuple(annotations.items())[-1][0]) # OK because annotations nonempty
    debug(prec_order.graph)
    debug(f'comparing {left_prec} <= {left_prec_inner} and {right_prec} <= {right_prec_inner} gives {prec_order.le(left_prec, left_prec_inner)} and {prec_order.le(right_prec, right_prec_inner)} = {prec_order.le(left_prec, left_prec_inner) and prec_order.le(right_prec, right_prec_inner)}')
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
        res += getattr(self, k).pretty(left_prec_inner, right_prec_inner, prec_order)
      else:
        assert type(v) is Str
        res += v.pretty
    return self.__class__.bracket(res) if bracketing else res
  def __str__(self): return self.pretty()
  c.__init__ = __init__
  c.__match_args__ = fields
  c.__repr__ = __repr__
  c.__eq__ = __eq__
  c.__str__ = __str__
  c.fresh = fresh
  c.subst = subst
  c.simple_names = simple_names
  c.fvs = fvs
  c.pretty = pretty
  for k in annotations:
    setattr(c, k, f'{name}.{k}')
  if not hasattr(c, 'bracket'):
    c.bracket = parens
  global global_parser
  global_parser.add_production((c, [None if type(v) is not Str else v.parse for k, v in annotations.items()]))
  return c

# ---------- Abstract binding trees ----------

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
  def __str__(self): return self.pretty()
  def fresh(self, renaming): return V(renaming[self.x]) if self.x in renaming else self
  def subst(self, substitution): return substitution[self.x] if self.x in substitution else self
  def simple_names(self, renaming={}, in_use=set()): return V(renaming[self.x]) if self.x in renaming else self
  def fvs(self): return {self.x}
  def pretty(self, left_prec='bot', right_prec='bot', prec_order=global_prec_order): return str(self.x)

class F:
  '''
  A binding form. There are two ways to construct instances of F:
  - F('x', lambda x: e[x]) represents a term e with free variable x.
    Constructs a value F(Name('x', n), e[V(Name('x', n))]) with n fresh.
  - F(x:Name, e) represents a term e with free variable x.
    Does not do any freshening.
  Pattern matching against an instance of F produces [x:Name, e:term] with x fresh.
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

  def __str__(self): return self.pretty()

  def fresh(self, renaming):
    x = self.x.fresh()
    e = self.e.fresh(renaming | {self.x: x})
    return F(x, e)

  def subst(self, substitution):
    x = self.x.fresh()
    e = self.e.subst(substitution | {self.x: V(x)})
    return F(x, e)

  def simple_names(self, renaming={}, in_use=set()):
    x = (
      self.x.with_n(None) if self.x.with_n(None) not in in_use else
      next(self.x.with_n(n) for n in nats() if self.x.with_n(n) not in in_use)
    )
    e = self.e.simple_names(renaming | {self.x: x}, in_use | {x})
    return F(x, e)

  def fvs(self):
    return self.e.fvs() - {self.x}

  def get_unwrap(self):
    e = self.fresh({})
    res = [e.x, e.e]
    return res
  def set_unwrap(self): assert False
  unwrap = property(get_unwrap, set_unwrap)

  def pretty(self, left_prec='bot', right_prec='bot', prec_order=global_prec_order):
    return f"{str(self.x)}. {self.e.pretty('bot', right_prec, prec_order)}"
  
  @staticmethod
  def transform(args):
    match args:
      case [V(x), e]: return F(x, e)
      case _: raise ValueError(f'F.transform({repr(args)})')

global_parser.add_production((F, [None, ". ", None]))

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

  simple_parens = lambda s: f'({s})'

  @mixfix
  class Top:
    s: Str('1')
    bracket = simple_parens
  prec_top(Top)
  prec_top(Top.s)

  @mixfix
  class Times:
    p: any
    times: Str(' * ')
    q: any
    bracket = simple_parens
  prec_ge(Times, Times.times) # right associative

  @mixfix
  class Plus:
    p: any
    plus: Str(' + ')
    q: any
    bracket = simple_parens
  prec_ge(Plus, Plus.plus) # right associative
  prec_ges([(Times, Plus), (Times.q, Plus.p), (Times.q, Plus.q)]) # * takes precedence over +

  @mixfix
  class Pow:
    p: any
    to: Str(' -> ')
    q: any
    bracket = simple_parens
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
  expect('1 * 1', Times(Top(), Top()).pretty())
  # * is right-associative
  expect('1 * 1 * 1', Times(Top(), Times(Top(), Top())).pretty())
  expect('(1 * 1) * 1', Times(Times(Top(), Top()), Top()).pretty())
  # + is right-associative
  expect('1 + 1 + 1', Plus(Top(), Plus(Top(), Top())).pretty())
  expect('(1 + 1) + 1', Plus(Plus(Top(), Top()), Top()).pretty())
  # * takes precedence over +
  expect('1 * (1 + 1)', Times(Top(), Plus(Top(), Top())).pretty())
  expect('(1 + 1) * 1', Times(Plus(Top(), Top()), Top()).pretty())
  expect('1 + 1 * 1', Plus(Top(), Times(Top(), Top())).pretty())
  expect('1 * 1 + 1', Plus(Times(Top(), Top()), Top()).pretty())
  # -> is right-associative
  expect('1 -> 1 -> 1', Pow(Top(), Pow(Top(), Top())).pretty())
  expect('(1 -> 1) -> 1', Pow(Pow(Top(), Top()), Top()).pretty())
  # * and + take precedence over -> on left
  expect('1 * 1 -> 1', Pow(Times(Top(), Top()), Top()).pretty())
  expect('1 * (1 -> 1)', Times(Top(), Pow(Top(), Top)).pretty())
  expect('1 + 1 -> 1', Pow(Plus(Top(), Top()), Top()).pretty())
  expect('1 + (1 -> 1)', Plus(Top(), Pow(Top(), Top())).pretty())
  # * and + do NOT take precedence over -> on right
  expect('1 -> (1 * 1)', Pow(Top(), Times(Top(), Top())).pretty())
  expect('1 -> (1 + 1)', Pow(Top(), Plus(Top(), Top())).pretty())

  # str() is same as .pretty()
  expect(True, Times(Top(), Top()).pretty() == str(Times(Top(), Top())))

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

  # Example 2: extending the language with quantifiers

  @mixfix
  class Forall:
    forall: Str('forall ')
    xp: F
    bracket = simple_parens
  @mixfix
  class Exists:
    forall: Str('exists ')
    xp: F
    bracket = simple_parens
  prec_ges([(Forall.xp, Exists.xp), (Exists.xp, Forall.xp)])
  @mixfix
  class Eq:
    m: any
    eq: Str(' = ')
    n: any
    bracket = simple_parens
  prec_ge(Eq.n, Exists.xp) # by transitivity, Eq.n >= Forall.xp
  prec_ge(Times.q, Exists.xp)

  p = Forall(F('x', lambda x: Exists(F('y', lambda y: Eq(x, y)))))
  expect('forall x@0. exists y@1. x@0 = y@1', p.pretty())
  expect('forall x. exists y. x = y', str(p.simple_names()))

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

  # Parsing of binding forms
  expect(F(Name('x'), V(Name('x'))), global_parser.parse('x. x'))
  expect(F(Name('x'), V(Name('y'))), global_parser.parse('x. y'))
  # The bad parse (x. x). x is discarded because the call to F.__init__ raises
  expect(F(Name('x'), F(Name('x'), V(Name('x')))), global_parser.parse('x. x. x')) 

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
  raises(lambda: global_parser.parse('forall x. forall y. exists z. (y = y) * x = y'))

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
        print(p)
        assert False

  p = Forall(F('x', lambda x: Forall(F('y', lambda y: Exists(F('z', lambda z: Times(Eq(y, y), Eq(x, y))))))))
  expect(set(), p.fvs())
  expect('forall x. forall y. exists z. (y = y) * (x = y)', str(p.simple_names()))
  p = simplify(p)
  expect('forall x. forall y. x = y', str(p.simple_names()))

  # Example 4: untyped LC

  @mixfix
  class Lam:
    lam: Str('\\')
    m: F
    bracket = simple_parens
  @mixfix
  class App:
    m: any
    app: Str(' ')
    n: any
    bracket = simple_parens
  prec_ge(App.n, App.m) # left-associative
  prec_ge(App.n, Lam.m) # application binds stronger than λ

  # Check printing of function applications
  id = Lam(F('x', lambda x: x))
  expect(r'(\x. x) ((\x. x) (\x. x))', str(App(id, App(id, id)).simple_names()))
  expect(r'(\x. x) (\x. x) (\x. x)', str(App(App(id, id), id).simple_names()))

  # One-step CBN reduction
  class Stuck(Exception): pass
  def step(m):
    match m:
      case Lam(F([x, m])): return Lam(F(x, step(m)))
      case App(Lam(F([x, m])), n): return m.subst({x: n})
      case App(m, n):
        try: return App(step(m), n)
        except Stuck: return App(m, step(n))
      case V(x): raise Stuck()

  expect(r'\x. x', str(step(App(id, id)).simple_names()))

  # Check capture-avoiding substitution on \y. (\x. \y. x) y
  k = lambda y: Lam(F('x', lambda x: Lam(F('y', lambda y: x))))
  v = lambda y: y
  m = Lam(F('y', lambda y: App(k(y), v(y))))
  expect(r'\y. (\x. \y@0. x) y', str(m.simple_names()))
  m = step(m)
  expect(r'\y. \y@0. y', str(m.simple_names()))

  # Omega Omega -> Omega Omega
  omega = Lam(F('x', lambda x: App(x, x)))
  expect(r'\x. x x', str(omega.simple_names()))
  omega2 = App(omega, omega)
  expect(r'(\x. x x) (\x. x x)', str(omega2.simple_names()))
  omega2 = step(omega2)
  expect(r'(\x. x x) (\x. x x)', str(omega2.simple_names()))

  # Parsing
  expect(omega, global_parser.parse(r'\x. x x'))
  expect(omega, global_parser.parse(r'\x. (x x)'))
  expect(omega2, global_parser.parse(r'(\x. (x x)) ((\x. (x x)))'))