from lark import Lark, Transformer, Tree
from ast import literal_eval
from lark.visitors import CollapseAmbiguities

# ---------- The running example from the tutorial ----------

json_parser = Lark(open('json.lark').read(), start='value')
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
  number = lambda self, n: float(n[0])

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

json_parser = Lark(open('json.lark').read(), start='value', tree_class=inline_transformer)
json = '{"key": ["s", "\\n", 3.14, true, null]}'
print(json_parser.parse(json))

# ---------- Trying out an ambiguous arithmetic grammar ----------

term_parser = Lark(open('amb.lark').read(), start='term')
print(term_parser.parse('1 + 1 + 1').pretty())
print(term_parser.parse('(1 + 1) + 1').pretty())
print(term_parser.parse('1 * 1 + 1').pretty())
print(term_parser.parse('1 + 1 * 1').pretty())
print('-'*10)
term_parser = Lark(open('amb.lark').read(), start='term', ambiguity='explicit')
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

term_parser = Lark(open('amb.lark').read(), start='term', tree_class=evaluate)
term = '1 + 1 + 1'
print(term_parser.parse(term))

# ---------- Trying out an ambiguous LC grammar ----------

term_parser = Lark(open('lc.lark').read(), start='term', ambiguity='explicit')
ts = term_parser.parse(r'(\x.x x) (\x. x x)')
print(ts.pretty())