from util import expect, raises
import syntax as S
from syntax import F, V, Name, Str, mixfix, Term

# Lambda calculus
@mixfix
class Lam(Term):
  lam: Str('\\', pretty='λ')
  m: F
@mixfix
class App(Term):
  m: any
  app: Str(' ')
  n: any
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
    case F([*xs, m]): return F(xs, parsteps(m))
    case Term(C, subterms): return C(*map(parsteps, subterms))

if __name__ == '__main__':

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
  expect(Pair(V(Name('y')), V(Name('x'))), parsteps(S.s(r'((\x. x) y, (\y. y) x)')))

  expect(Lam(F('x', lambda x: Lam(F('y', lambda y: y)))), desugar(S.s(r'\x y. y')))