from util import expect, raises
import syntax as S
from syntax import F, V, Name, Str, mixfix, Term

# ---------- Logic ----------

@mixfix
class Top(Term):
  s: Str('true', tex=r'\top ', pretty='T')
S.prec_top(Top)
S.prec_top(Top.s)

@mixfix
class And(Term):
  p: Term
  land: Str('/\\', tex=r'\land ', pretty=' ∧ ')
  q: Term
S.prec_ge(And, And.land) # right associative

@mixfix
class Or(Term):
  p: Term
  lor: Str('\\/', tex=r'\lor ', pretty=' ∨ ')
  q: Term
S.prec_ge(Or, Or.lor) # right associative
S.prec_pairwise_ge([And, And.p, And.land, And.q], [Or, Or.p, Or.lor, Or.q])

@mixfix
class To(Term):
  p: Term
  to: Str('->', tex='\to ', pretty=' → ')
  q: Term
S.prec_ge(To, To.to) # right associative
S.prec_ges([(Or, To), (Or.q, To.p), (Or, To.to), (Or.q, To.q)]) # \/ takes precedence over ->
# Note: by transitivity, also get that /\ takes precedence over ->.

@mixfix
class Forall(Term):
  forall: Str('forall ', tex=r'\forall ', pretty='∀ ')
  xp: F
@mixfix
class Exists(Term):
  exists: Str('exists ', tex=r'\exists ', pretty='∃ ')
  xp: F
S.prec_ges([(Forall.xp, Exists.xp), (Exists.xp, Forall.xp)])
@mixfix
class Eq(Term):
  m: Term
  eq: Str('=', pretty=' = ')
  n: Term
S.prec_pairwise_ge([Eq], [And, And.land, Exists.exists])
S.prec_pairwise_ge([Eq.n], [And.p, And.q, Exists.xp])
S.prec_ge(And.q, Exists.xp)

# Lambda calculus
@mixfix
class Lam(Term):
  lam: Str('\\', tex=r'\lambda ', pretty='λ')
  m: F
@mixfix
class App(Term):
  m: Term
  app: Str(' ')
  n: Term
S.prec_ge(App.n, App.m) # left-associative
S.prec_ge(App.n, Lam.m) # application binds stronger than λ

# Desugar variable-length binders to single binders
def desugar(m):
  match m:
    case Lam(F([x, m])): return Lam(F(x, desugar(m)))
    case Lam(F([x, y, *ys, m])): return Lam(F(x, desugar(Lam(F(y, *ys, m)))))
    case V(_): return m
    case Term(C, ms): return C(*map(desugar, ms))
    case _: assert False

# One-step reduction, defined strictly on lambda-terms
class Stuck(Exception): pass
def step(m):
  match m:
    case Lam(F([x, m])): return Lam(F(x, step(m)))
    case App(Lam(F([x, m])), n): return m.subst({x: n})
    case App(m, n):
      try: return App(step(m), n)
      except Stuck: return App(m, step(n))
    case V(x): raise Stuck()
    case _: raise ValueError(m)

# Complete development
def parsteps(m):
  match m:
    case Lam(F([x, m])): return Lam(F(x, parsteps(m)))
    case App(Lam(F([x, m])), n): return parsteps(m).subst({x: parsteps(n)})
    case App(m, n): return App(parsteps(m), parsteps(n))
    case V(_): return m
    case F([*xs, m]): return F(*xs, parsteps(m))
    case Term(C, subterms): return C(*map(parsteps, subterms))

# ---------- Navigation ----------

@mixfix
class Cursor:
  l: Str('[', tex=r'{\color{red}', pretty='[')
  m: Term
  r: Str(']', tex=r'}', pretty=']')
S.prec_top(Cursor)
S.prec_bot(Cursor.l)
S.prec_bot(Cursor.m)
S.prec_top(Cursor.r)

def move_down(m):
  match m:
    case V(_): return m
    case F([*xs, m]): return F(*xs, m)
    case Cursor(Term(C, [m, *ms])): return C(Cursor(m), *ms)
    case Term(C, ms): return C(*map(move_down, ms))

def move_right(m):
  def find_cursor(ms):
    try:
      i = next(i for i, m in enumerate(ms) if type(m) is Cursor)
      return ms[:i], ms[i].m, ms[i+1:]
    except StopIteration: return None
  match m:
    case V(_): return m
    case F([*xs, m]): return F(*xs, m)
    case Term(C, ms):
      match find_cursor(ms):
        case (l, m, [n, *r]): return C(*l, m, Cursor(n), *r)
        case None: return C(*map(move_right, ms))

if __name__ == '__main__':

  # ---------- Logic ----------

  p = Forall(F('x', lambda x: Exists(F('y', lambda y: Eq(x, y)))))
  expect('∀ x_{0}. ∃ y_{1}. x_{0} = y_{1}', p.str('pretty'))
  expect('∀ x. ∃ y. x = y', p.simple_names().str('pretty'))

  # Equality up to renaming
  mxy = Forall(F('x', lambda x: Forall(F('y', lambda y: Eq(x, y)))))
  muv = Forall(F('u', lambda u: Forall(F('v', lambda v: Eq(u, v)))))
  muv_flip = Forall(F('u', lambda u: Forall(F('v', lambda v: Eq(v, u)))))
  expect(True, mxy == muv)
  expect(False, mxy == muv_flip)

  # Parsing of C identifiers as variable names
  expect(V(Name('a')), S.s('a'))
  expect(V(Name('snake_case123')), S.s('snake_case123'))
  expect(V(Name('_abc')), S.s('_abc'))

  expect('x = y ∨ z = w', S.s('x = y \\/ z = w').str('pretty'))

  # Parsing of quantified formulas
  # Note: tests are happening up to renaming of bound variables, because
  # F.__eq__ works up to renaming
  expect(Forall(F('x', lambda x: x)), S.s('forall x. x'))
  expect(Exists(F('x', lambda x: x)), S.s('exists x. x'))
  expect(Forall(F('p', lambda p: And(p, p))), S.s(r'forall x. x /\ x'))
  expect(Forall(F('x', lambda x: Exists(F('y', lambda y: Eq(x, y))))), S.s('forall x. exists y. x = y'))
  expect(
    Forall(F('x', lambda x: Forall(F('y', lambda y: Exists(F('z', lambda z: And(Eq(y, y), Eq(x, y)))))))), 
    S.s(r'forall x. forall y. exists z. y = y /\ x = y')
  )

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
      case Or(p, q): return Or(simplify(p), simplify(q))
      case And(p, q):
        match simplify(p), simplify(q):
          case Top(), Top(): return Top()
          case Top(), q: return q
          case p, Top(): return p
          case p, q: return And(p, q)
      case To(p, q): return To(simplify(p), simplify(q))
      case _:
        assert False

  p = Forall(F('x', lambda x: Forall(F('y', lambda y: Exists(F('z', lambda z: And(Eq(y, y), And(Eq(x, y), Eq(z, z)))))))))
  expect(set(), p.fvs())
  expect('∀ x. ∀ y. ∃ z. y = y ∧ x = y ∧ z = z', p.simple_names().str('pretty'))
  p = simplify(p)
  expect('∀ x. ∀ y. x = y', p.simple_names().str('pretty'))

  # ---------- Lambda calculus ----------

  # str uses \ and condensed . while pretty uses λ
  one = Lam(F('x', lambda x: x))
  expect('λx. x', one.simple_names().str('pretty'))
  expect(r'\x.x', str(one.simple_names()))

  # Check printing of function applications
  expect('(λx. x) ((λx. x) (λx. x))', App(one, App(one, one)).simple_names().str('pretty'))
  expect('(λx. x) (λx. x) (λx. x)', App(App(one, one), one).simple_names().str('pretty'))

  expect('λx. x', step(App(one, one)).simple_names().str('pretty'))

  # Check capture-avoiding substitution on \y. (\x. \y. x) y
  k = lambda y: Lam(F('x', lambda x: Lam(F('y', lambda y: x))))
  v = lambda y: y
  m = Lam(F('y', lambda y: App(k(y), v(y))))
  expect('λy. (λx. λy_{0}. x) y', m.simple_names().str('pretty'))
  m = step(m)
  expect('λy. λy_{0}. y', m.simple_names().str('pretty'))

  # Omega Omega -> Omega Omega
  omega = Lam(F('x', lambda x: App(x, x)))
  expect('λx. x x', omega.simple_names().str('pretty'))
  omega2 = App(omega, omega)
  expect('(λx. x x) (λx. x x)', omega2.simple_names().str('pretty'))
  omega2 = step(omega2)
  expect('(λx. x x) (λx. x x)', omega2.simple_names().str('pretty'))

  # Parsing
  expect(omega, S.s(r'\x. x x'))
  expect(omega, S.s(r'\x. (x x)'))
  expect(omega2, S.s(r'(\x. (x x)) ((\x. (x x)))'))
  expect(App(App(one, one), one), S.s(r'(\x.x) (\x.x) (\x.x)'))
  # Even though the production for App is term -> term term, this still has a
  # unique parse because parsing of identifiers always takes the longest match
  expect(V(Name('xy')), S.s(r'xy'))

  # Recognizes the outer parens as superfluous and spaces unnecessary
  expect(
    Lam(F('f', lambda f: App(Lam(F('x', lambda x: x)), f))),
    S.s(r'(\f.(\x.x) f)')
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
  expect(snd_y, S.s(r'(\y.\p.p) (\f.(\x.f (x x)) (\x.f (x x)))'))
  expect(
    App(snd_y, is_zero),
    S.s(r'(\y.\p.p) (\f.(\x.f (x x)) (\x.f (x x))) (\n.n (\t.\f.t) (\n.\t.\f.f))')
  )

  def parsed_efficiently(s):
    _, stats = S.s(s, with_stats=True)
    # Parse was completely unambiguous
    expect(1, stats.trees)
    expect(0, stats.duplicates)
    # contract() and coalesce() both converged quickly
    expect(2, stats.contract_steps)
    expect(1, stats.coalesce_steps)

  # Long input that can't be parsed efficiently without good grammar generation
  parsed_efficiently(' '.join(r'''
    (\Y.\iszero.\add.\z.\s.\cons.\fst.\snd.
      (\pred.
        (\tri. tri (s (s (s z))))
        (Y (\tri.\n.iszero n z (add n (tri (pred n))))))
      (\n.fst (n (\p. cons (snd p) (s (snd p))) (cons z z))))
    (\f.(\x.(f (x x))) (\x.(f (x x))))
    (\n.n (\n.\t.\f.f) (\t.\f.t))
    (\m.\n.\s.\z.m s (n s z))
    (\s.\z.z)
    (\n.\s.\z.s (n s z))
    (\x.\y.\f.f x y)
    (\p.p (\x.\y.x))
    (\p.p (\x.\y.y))
  '''.split()))

  # Manually contracting SPPF avoids exponential blowups in the number of parse trees
  parsed_efficiently('(a) (b) (c) (d) (e) (f) (g) (h) (i) (j) (k) (l)')
  # This example requires the custom graph shenanigans; lark's visitors will
  # perform DFS and lead to exponential time
  parsed_efficiently('((((((((a))))))))') 

  # Variable-length binding forms
  expect(Lam(F('x', 'y', lambda x, y: x)), S.s(r'\x y.x'))
  raises(lambda: S.s(r'\.x')) # length-0 binding forms not allowed
  def f():
    match S.s(r'\x y.x'):
      case Lam(F([x, y, e])): return Lam(F(y, x, e))
  expect(S.s(r'\y x.x'), f()) # matching

  @mixfix
  class Pair(Term):
    l: Str('(', pretty='\\langle ')
    m: Term
    comma: Str(',')
    n: Term
    r: Str(')', pretty='\\rangle ')
  S.prec_pairwise_ge([App.n], [Pair.l, Pair.m, Pair.comma, Pair.n, Pair.r])
  S.prec_pairwise_ge([App], [Pair.l, Pair.m, Pair.comma, Pair.n, Pair.r])
  
  expect(Pair(V(Name('x')), V(Name('y'))), S.s('(x, y)'))
  expect(Pair(V(Name('x')), V(Name('y'))), S.s('(((((((((x, y)))))))))'))
  parsed_efficiently('(((((((((x, y)))))))))')
  expect(Pair(V(Name('y')), V(Name('x'))), parsteps(S.s(r'((\x. x) y, (\y. y) x)')))

  expect(Lam(F('x', lambda x: Lam(F('y', lambda y: y)))), desugar(S.s(r'\x y. y')))
  parsed_efficiently(r'\x y. y')

  # ---------- Navigation ----------

  p = Cursor(S.s(r'x = y /\ y = z'))
  p = move_down(p)
  p = move_right(p)
  expect('x = y ∧ [y = z]', p.str('pretty'))