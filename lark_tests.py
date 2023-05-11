from lark import Lark, Transformer, Tree
from ast import literal_eval

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

# ---------- Trying out a highly ambiguous grammar ----------

json_parser = Lark(open('amb.lark').read(), start='value', tree_class=inline_transformer)
json = '{"key": ["s", "\\n", 3.14, true, null]}'
print(json_parser.parse(json))