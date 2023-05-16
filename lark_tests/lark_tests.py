from lark import Lark, Transformer, Tree
from ast import literal_eval
from lark.visitors import CollapseAmbiguities

# ---------- The running example from the tutorial ----------

json_lark = '''
  ?value : dict
         | list
         | string
         | SIGNED_NUMBER -> number
         | "true" -> true
         | "false" -> false
         | "null" -> null
  
  list : "[" [value ("," value)*] "]"
  
  dict : "{" [pair ("," pair)*] "}"
  pair : string ":" value
  
  string : ESCAPED_STRING
  
  %import common.ESCAPED_STRING
  %import common.SIGNED_NUMBER
  %import common.WS
  %ignore WS
'''

json_parser = Lark(json_lark, start='value')
json = '{"key": ["s", "\\n", 3.14, true, null]}'
print(json_parser.parse(json))
print(json_parser.parse(json).pretty())

class T(Transformer):
  list = list
  pair = tuple
  dict = dict
  null = lambda self, _: None
  true = lambda self, _: True
  false = lambda self, _: False
  string = lambda self, s: literal_eval(s[0])

setattr(T, 'number', lambda self, n: float(n[0]))

print(T().transform(json_parser.parse(json)))

# ---------- Inlining the transformer ----------

def inline_transformer(f, xs):
  match f:
    case 'string': return literal_eval(xs[0])
    case 'number': return float(xs[0])
    case 'null': return None
    case 'true': return True
    case 'false': return False
    case 'list': return list(xs)
    case 'pair': return tuple(xs)
    case 'dict': return dict(xs)
    case _: return Tree(f, xs)

json_parser = Lark(json_lark, start='value', tree_class=inline_transformer)
json = '{"key": ["s", "\\n", 3.14, true, null]}'
print(json_parser.parse(json))

# ---------- Trying out an ambiguous arithmetic grammar ----------

amb_lark = '''
  ?term : literal
  | term "+" term -> add
  | term "-" term -> sub
  | term "*" term -> mul
  | term "/" term -> div
  | "(" term ")"
  
  ?literal : string
  | SIGNED_NUMBER -> number
  | "true" -> true
  | "false" -> false
  
  string : ESCAPED_STRING
  
  %import common.ESCAPED_STRING
  %import common.SIGNED_NUMBER
  %import common.WS
  %ignore WS
'''

term_parser = Lark(amb_lark, start='term')
print(term_parser.parse('1 + 1 + 1').pretty())
print(term_parser.parse('(1 + 1) + 1').pretty())
print(term_parser.parse('1 * 1 + 1').pretty())
print(term_parser.parse('1 + 1 * 1').pretty())
print('-'*10)
term_parser = Lark(amb_lark, start='term', ambiguity='explicit')
ts = term_parser.parse('1 * 1 + 1 + 1')
for t in CollapseAmbiguities().transform(ts): print(t.pretty())
print(ts)
print(ts.pretty())

def evaluate(op, xs):
  match op, xs:
    case 'add', [x, y]: return x + y
    case 'sub', [x, y]: return x - y
    case 'mul', [x, y]: return x * y
    case 'div', [x, y]: return x / y
    case 'div', [x, y]: return x / y
    case 'string', _: return 0
    case 'true', _: return 1
    case 'false', _: return 0
    case 'number', [x]: return float(x)
    case _, _: assert False

term_parser = Lark(amb_lark, start='term', tree_class=evaluate)
term = '1 + 1 + 1'
print(term_parser.parse(term))

# ---------- Trying out an ambiguous LC grammar ----------

lc_lark = r'''
  ?term : literal
  | term " " term
  | "\\" term "." term
  | "(" term ")"

  ?literal : CNAME -> identifier
  | SIGNED_NUMBER -> number

  %import common.CNAME
  %import common.SIGNED_NUMBER
  %import common.WS
  %ignore WS
'''

term_parser = Lark(lc_lark, start='term', ambiguity='explicit')
ts = term_parser.parse(r'(\x.x x) (\x. x x)')
print(ts.pretty())

# ---------- Trying out a factored grammar ----------

term_parser = Lark(r'''
  ?term : sum
  ?sum : product "+" term
        | product
  ?product : atom "*" product
          | atom
  ?atom : SIGNED_NUMBER -> number
       | "(" term ")"

  %import common.SIGNED_NUMBER
  %import common.WS
  %ignore WS
''', start='term', parser='lalr')
ts = term_parser.parse(r'1 * 2 + 3')
print(ts.pretty())
ts = term_parser.parse(r'1 + 2 + 3')
print(ts.pretty())
ts = term_parser.parse(r'(1 + 2) + 3')
print(ts.pretty())

# ---------- Factored grammar for LC? ----------

term_parser = Lark(r'''
  ?term : lam | app
  ?app1 : atom
  ?app : app app1 | app1
  f_lam : name "." lam1
  lam : "λ" f_lam
  ?lam1 : lam | app
  ?atom : name
       | "(" term ")"
  name : /[a-z]/

  %import common.WS
  %ignore WS
''', start='term', parser='lalr')
ts = term_parser.parse('λx.x')
print(ts.pretty())
ts = term_parser.parse('λx.λy.xy')
print(ts.pretty())
ts = term_parser.parse('λf.λg.λx.fx(gx)')
print(ts.pretty())
ts = term_parser.parse('(λy.λp.p)(λf.(λx.f(xx))(λx.f(xx)))(λn.n(λt.λf.t)(λn.λt.λf.f))')
print(ts.pretty())

# ---------- Auto-factored grammar for arith ----------

term_parser = Lark(r'''
      ?term : term_22_22
      
      ?term_22_22 : term_5_8
      | term_9_12
      | term_13_16
      | term_17_16
      | term_19_15

      ?term_5_8 : term_5_6 "+" term_7_8 -> c_plus
      | term_1_4

      ?term_5_6 : term_1_4

      ?term_1_4 : term_1_2 "*" term_3_4 -> c_times
      | term_0_0

      ?term_1_2 : term_0_0

      ?term_0_0 : atom
      | "1" -> c_top

      ?term_3_4 : term_1_4

      ?term_7_8 : term_5_8

      ?term_9_12 : term_9_10 "->" term_11_12 -> c_pow
      | term_0_0

      ?term_9_10 : term_5_8

      ?term_11_12 : term_9_12

      ?term_13_16 : "forall " term_14_16 -> c_forall
      | term_0_0

      ?term_14_16 : term_0_0

      ?term_17_16 : "exists " term_18_16 -> c_exists
      | term_0_0

      ?term_18_16 : term_0_0

      ?term_19_15 : term_19_20 "=" term_21_15 -> c_eq
      | term_0_0

      ?term_19_20 : term_0_0

      ?term_21_15 : term_0_0

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
''', start='term', ambiguity='explicit')
ts = term_parser.parse(r'1 * 2 + 3')
print(ts.pretty())
ts = term_parser.parse(r'1 + 2 + 3')
print(ts.pretty())
ts = term_parser.parse(r'(1 + 2) + 3')
print(ts.pretty())
ts = term_parser.parse(r'(z + y) + x')
print(ts.pretty())
ts = term_parser.parse(r'1 -> 2 -> 3')
print(ts.pretty())
ts = term_parser.parse(r'1 + 2 -> 3')
print(ts.pretty())
ts = term_parser.parse(r'1 -> (2 + 3)')
print(ts.pretty())
ts = term_parser.parse(r'1 -> (2 + 3)')
print(ts.pretty())
