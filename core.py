# ---------- Mixfix printing ----------
#
# The decorator @mixfix adds mixfix precedence-based printing for dataclasses.
#
# For example, to declare an operator And(p, q) that pretty-prints as p + q:
#   @mixfix
#   class And:
#     p: any
#     plus: str(' + ')
#     q: any
# By default, precedence mismatches are mediated by inserting parentheses using
def parens(s): return f'\\left({s}\\right)'
# but one can specify a different 'bracketer' using the optional field 'bracket', e.g.
#   @mixfix
#   class Add:
#     p: any
#     plus: str(' + ')
#     q: any
#     bracket = lambda s: f'({s})'
# to get ordinary parentheses instead of the LaTeX ones.

# Precedences are declared as a partial ordering on 'cursor positions',
# which correspond to positions in the string produced by pretty-printing.
# Each field refers to the cursor position immediately after it in the
# pretty-printed string; the class name ('Add' in this case) is used to refer to
# the left-most cursor position. For example, visualizing the cursor position as |,
#    Add        refers to   |p + q
#    Add.p      refers to    p|+ q
#    Add.plus   refers to    p +|q
#    Add.q      refers to    p + q|
# The pretty-printer uses the partial ordering on cursor positions to decide
# which brackets can be omitted. For example, adding the inequality Add >
# Add.plus specifies right associativity: it allows the brackets in
#   p + (q + r)
# to be omitted because the cursor position
#   Add = |q + r
# has higher precedence than the cursor position
#   Add.plus = p +|(q+r)
# TODO describe pretty-printing algorithm via incoming and outgoing precedences

from poset import Poset
global_prec_order = Poset().add_bot('bot').add_top('top')
def to_prec(p): return p.__name__ if type(p) is type else p
def prec_ge(p, q): global_prec_order.add(to_prec(q), to_prec(p))
def prec_ges(pqs):
  for p, q in pqs:
    prec_ge(p, q)
def prec_bot(p): global_prec_order.add_bot(to_prec(p))
def prec_top(p): global_prec_order.add_top(to_prec(p))

def mixfix(c):
  '''
  Given a class declaration
    class C:
      x: tx
      y: str(s)
      z: tz
      etc
  Generates a dataclass with
  - fields x: t, z: tz, ... (fields with 'string literal type' omitted)
  - method fresh(renaming) that freshens all bound variables (instances of the class F) in each field
  - method subst(**substitution) that applies the given substitution
  - method simple_names(renaming, renaming_used) that maximally simplifies disambiguators on bound variable names
  - method pretty() that pretty-prints an instance of C, omitting brackets as allowed by the global precedence order
  - class properties x, y, z, ... for referring to cursor positions denoted by these fields
  - class property __match_args__ = ('x', 'z', ...) for pattern matching against instances of C
  '''
  name = c.__name__
  annotations = c.__annotations__
  # Luckily, despite being a dict, c.__annotations__ contains items in declaration order,
  # so the order of the mixfix operators is preserved
  fields = tuple(k for k, v in annotations.items() if type(v) is not str)
  def init(self, *args):
    assert len(fields) == len(args)
    for k, arg in zip(fields, args):
      setattr(self, k, arg)
  def fresh(self, renaming):
    return self.__class__(*(getattr(self, k).fresh(renaming) for k in fields))
  def subst(self, substitution):
    return self.__class__(*(getattr(self, k).subst(substitution) for k in fields))
  def simple_names(self, renaming={}, renaming_used=set()):
    return self.__class__(*(getattr(self, k).simple_names(renaming, renaming_used) for k in fields))
  def pretty(self, left_prec='bot', right_prec='bot', prec_order=global_prec_order):
    def cons(x, g):
      yield x
      yield from g
    def make_prec(field_name): return f'{name}.{field_name}' if field_name != name else name
    # Compute left and right prec for each item
    # print(list(
    #   (make_prec(j), make_prec(k), (k, v))
    #   for (j, _), (k, v) in zip(cons((name, ''), annotations.items()), annotations.items())
    # ))
    items = (
      (make_prec(j), make_prec(k), (k, v))
      for (j, _), (k, v) in zip(cons((name, ''), annotations.items()), annotations.items())
    )
    res = ''
    for (left_prec_inner, right_prec_inner, (k, v)) in items:
      if type(v) is str:
        res += v
      else:
        res += getattr(self, k).pretty(left_prec_inner, right_prec_inner, prec_order)
    if len(annotations) == 0: return res
    else:
      left_prec_inner = name
      right_prec_inner = make_prec(tuple(annotations.items())[-1][0])
      # print(f'res = {res}')
      # print(prec_order.graph)
      # print(f'comparing {left_prec} <= {left_prec_inner} and {right_prec} <= {right_prec_inner} gives {prec_order.le(left_prec, left_prec_inner)} and {prec_order.le(right_prec, right_prec_inner)} = {prec_order.le(left_prec, left_prec_inner) and prec_order.le(right_prec, right_prec_inner)}')
      if prec_order.le(left_prec, left_prec_inner) and prec_order.le(right_prec, right_prec_inner):
        return res
      else:
        return self.__class__.bracket(res)
  c.__init__ = init
  c.__match_args__ = fields
  c.fresh = fresh
  c.subst = subst
  c.simple_names = simple_names
  c.pretty = pretty
  for k in annotations:
    setattr(c, k, f'{name}.{k}')
  if not hasattr(c, 'bracket'):
    c.bracket = parens
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
  - n is a disambiguator used to ensure that bound variables are globally fresh
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
  Usually not invoked explicitly; see F below.
  '''
  __match_args__ = ('x',)
  def __init__(self, x): self.x = x
  def __eq__(self, other): return self.x == other.x
  def __repr__(self): return f'V({repr(self.x)})'
  def fresh(self, renaming): return V(renaming[self.x]) if self.x in renaming else self
  def subst(self, substitution): return substitution[self.x] if self.x in substitution else self
  def simple_names(self, renaming={}, renaming_used=set()): return V(renaming[self.x]) if self.x in renaming else self
  def pretty(self, left_prec='bot', right_prec='bot', prec_order=global_prec_order): return str(self.x)

class F:
  '''
  A binder.
  F('x', lambda x: e[x]) represents a term e with free variable x.
  Desugars to F(Name('x', n), e[V(Name('x', n))]) with n fresh.
  Pattern matching against an instance of F produces [x:Name, e:term] with x fresh.
  '''
  __match_args__ = ('unwrap',)
  def __init__(self, x, f, raw=False):
    if raw:
      [self.x, self.e] = [x, f]
    else:
      self.x = Name(x).fresh()
      self.e = f(V(self.x))

  def __repr__(self):
    return f'F([{repr(self.x)}, {repr(self.e)}])'

  def fresh(self, renaming):
    x = self.x.fresh()
    e = self.e.fresh(renaming | {self.x: x})
    return F(x, e, raw=True)

  def subst(self, substitution):
    x = self.x.fresh()
    e = self.e.subst(substitution | {self.x: V(x)})
    return F(x, e, raw=True)

  def simple_names(self, renaming={}, renaming_used=set()):
    x = (
      self.x.with_n(None) if self.x.with_n(None) not in renaming_used else
      next(self.x.with_n(n) for n in nats() if self.x.with_n(n) not in renaming_used)
    )
    e = self.e.simple_names(renaming | {self.x: x}, renaming_used | {x})
    return F(x, e, raw=True)

  def get_unwrap(self):
    e = self.fresh({})
    res = [e.x, e.e]
    return res
  def set_unwrap(self): assert False
  unwrap = property(get_unwrap, set_unwrap)

  def pretty(self, left_prec='bot', right_prec='bot', prec_order=global_prec_order):
    return f"{str(self.x)}. {self.e.pretty('bot', right_prec, prec_order)}"

if __name__ == '__main__':
  # Example: precedence-based printing for simple types
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
    s: str('1')
    bracket = simple_parens
  prec_top(Top)
  prec_top(Top.s)

  @mixfix
  class Times:
    p: any
    times: str(' * ')
    q: any
    bracket = simple_parens
  prec_ge(Times, Times.times) # right associative

  @mixfix
  class Plus:
    p: any
    plus: str(' + ')
    q: any
    bracket = simple_parens
  prec_ge(Plus, Plus.plus) # right associative
  prec_ges([(Times, Plus), (Times.q, Plus.p), (Times.q, Plus.q)]) # * takes precedence over +

  @mixfix
  class Pow:
    p: any
    to: str(' -> ')
    q: any
    bracket = simple_parens
  prec_ge(Pow, Pow.to) # right associative
  prec_ges([(Plus, Pow), (Plus.q, Pow.p)]) # + takes precedence on left of ->
  # Note: by transitivity, also get that * takes precedence on left of ->.

  def expect(want, have):
    if want != have:
      raise Exception(f'\nWant: {want}\nHave: {have}')

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

  # Example: extending the language with quantifiers

  @mixfix
  class Forall:
    forall: str('forall ')
    xp: F
  @mixfix
  class Exists:
    forall: str('exists ')
    xp: F
  prec_ges([(Forall.xp, Exists.xp), (Exists.xp, Forall.xp)])
  @mixfix
  class Eq:
    m: any
    eq: str(' = ')
    n: any
  prec_ge(Eq.n, Exists.xp) # by transitivity, Eq.n >= Exists.xp

  # def pretty(p):
  #   match p:
  #     case And(p, q): return f'({pretty(p)} \\land {pretty(q)})'
  #     case Or(p, q): return f'({pretty(p)} \\lor {pretty(q)})'
  #     case Implies(p, q): return f'({pretty(p)} \\to {pretty(q)})'
  #     case Eq(m, n): return f'({pretty(m)} = {pretty(n)})'
  #     case V(x): return f'{x}'
  #     case Forall(F([x, p])): return f'\\forall {x}. {pretty(p)}'
  #     case Exists(F([x, p])): return f'\\exists {x}. {pretty(p)}'
  #     case _:
  #       print(p)
  #       assert False

  p = Forall(F('x', lambda x: Exists(F('y', lambda y: Eq(x, y)))))
  expect('forall x@0. exists y@1. x@0 = y@1', p.pretty())
  expect('forall x. exists y. x = y', p.simple_names().pretty())