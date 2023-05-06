def nats():
  n = 0
  while True:
    yield n
    n += 1
nats = nats()

class Name:
  def __init__(self, x):
    self.x = x
    self.n = next(nats)
  def __hash__(self): return hash((self.x, self.n))
  def __eq__(self, other): return self.x == other.x and self.n == other.n
  def __repr__(self): return f'Name({self.x}, {self.n})'
  def __str__(self): return f'{self.x}@{self.n}'
  def fresh(self): return Name(self.x)

class V:
  __match_args__ = ('x',)
  def __init__(self, x): self.x = x
  def __eq__(self, other): return self.x == other.x
  def __repr__(self): return f'V({repr(self.x)})'
  def fresh(self, renaming):
    return V(renaming[self.x]) if self.x in renaming else self

class F:
  __match_args__ = ('unwrap',)
  def __init__(self, x, f, raw=False):
    if raw:
      [self.x, self.e] = [x, f]
    else:
      self.x = Name(x)
      self.e = f(V(self.x))

  def __repr__(self):
    return f'F([{repr(self.x)}, {repr(self.e)}])'

  def fresh(self, renaming):
    x = self.x.fresh()
    e = self.e.fresh(renaming | {self.x: x})
    return F(x, e, raw=True)

  def get_unwrap(self):
    e = self.fresh({})
    res = [e.x, e.e]
    return res
  def set_unwrap(self): assert False
  unwrap = property(get_unwrap, set_unwrap)

from dataclasses import dataclass

class Term:
  def fresh(self, renaming):
    return self.__class__(**{k: getattr(self, k).fresh(renaming) for k, v in self.__annotations__.items() if type(v) is not str})

@dataclass
class And(Term):
  p: Term
  q: Term
@dataclass
class Or(Term):
  p: Term
  q: Term
@dataclass
class Implies(Term):
  p: Term
  q: Term
@dataclass
class Eq(Term):
  m: Term
  n: Term
@dataclass
class Forall(Term):
  xp: Term
@dataclass
class Exists(Term):
  xp: Term

def pretty(p):
  match p:
    case And(p, q): return f'({pretty(p)} \\land {pretty(q)})'
    case Or(p, q): return f'({pretty(p)} \\lor {pretty(q)})'
    case Implies(p, q): return f'({pretty(p)} \\to {pretty(q)})'
    case Eq(m, n): return f'({pretty(m)} = {pretty(n)})'
    case V(x): return f'{x}'
    case Forall(F([x, p])): return f'\\forall {x}. {pretty(p)}'
    case Exists(F([x, p])): return f'\\exists {x}. {pretty(p)}'
    case _:
      print(p)
      assert False

p = Forall(F('x', lambda x: Exists(F('y', lambda y: Eq(x, y)))))
print(pretty(p))

# Ideally, have decorator that allows declaring mixfix constructors like
# @mixfix
# class Exists(Term):
#   prec p
#   '\\exists'
#   prec q
#   xp: Term
#   prec r

print(eval('pretty(p)'))

# class Add(Term):
#   p: Term
#   land: '\\land'
#   q: Term
# Each field refers to the precedence of the cursor position immediately after it.
# The special field 'Add' (or the name of the class in general) is used to refer
# to the left-most cursor position.
# For example, to specify right associativity, add inequality Add.land <= Add.
# Luckily, despite being a dict, c.__annotations__ contains items in declaration order,
# so class definitions like the above can be parsed as mixfix declarations.

def parens(s): return f'\\left({s}\\right)'

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
  name = c.__name__
  annotations = c.__annotations__
  fields = tuple(k for k, v in annotations.items() if type(v) is not str)
  def init(self, *args):
    assert len(fields) == len(args)
    for k, arg in zip(fields, args):
      setattr(self, k, arg)
  def fresh(self, renaming):
    return self.__class__(*(getattr(self, k).fresh(renaming) for k in fields))
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
  c.pretty = pretty
  for k in annotations:
    setattr(c, k, f'{name}.{k}')
  if not hasattr(c, 'bracket'):
    c.bracket = parens
  return c

@mixfix
class Top:
  s: str('\\top ')
prec_top(Top)
prec_top(Top.s)

@mixfix
class Times:
  p: any
  times: str('\\times ')
  q: any
prec_ge(Times, Times.times) # right associative

@mixfix
class Plus:
  p: any
  plus: str('+')
  q: any
prec_ge(Plus, Plus.plus) # right associative
prec_ges([(Times, Plus), (Times.q, Plus.p), (Times.q, Plus.q)]) # multiplication > addition

@mixfix
class Pow:
  p: any
  to: str('\\to ')
  q: any
prec_ge(Pow, Pow.to) # right associative
prec_ges([(Plus, Pow), (Plus.q, Pow.p)]) # transitively also get p /\ q -> r w/o parens

print(Times.__name__)
match Times(Top(), Top()):
  case Times(p, q): print(p, q)

print(Times(Top(), Top()).pretty())
print(Times(Top(), Times(Top(), Top())).pretty())
print(Times(Times(Top(), Top()), Top()).pretty())
print()
print(Times(Top(), Plus(Top(), Top())).pretty())
print(Times(Plus(Top(), Top()), Top()).pretty())
print()
print(Plus(Top(), Times(Top(), Top())).pretty())
print(Plus(Times(Top(), Top()), Top()).pretty())
print()
print(Pow(Top(), Pow(Top(), Top())).pretty())
print(Pow(Pow(Top(), Top()), Top()).pretty())
print()
print(Pow(Times(Top(), Top()), Top()).pretty())
print(Pow(Plus(Top(), Top()), Top()).pretty())