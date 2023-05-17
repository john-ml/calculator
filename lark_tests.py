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

# ---------- Playing with SPPFs ----------

term_parser = Lark(r'''
      ?term : term_5_8
      | term_9_12
      | term_13_16
      | term_17_16
      | term_19_15
      | term_22_25
      | term_26_24

      ?term_5_8 : term_1_4 "+" term_5_8 -> c_plus
      | term_1_4

      ?term_1_4 : term_0_0 "*" term_1_4 -> c_times
      | term_0_0

      ?term_0_0 : atom
      | "1" -> c_top

      ?term_9_12 : term_5_8 "->" term_9_12 -> c_pow
      | term_0_0

      ?term_13_16 : "forall " name "." term_29_16 -> c_forall
      | term_0_0

      ?term_29_16 : term_13_16
      | term_17_16
      | term_1_4
      | term_19_15

      ?term_17_16 : "exists " name "." term_29_16 -> c_exists
      | term_0_0

      ?term_19_15 : term_0_0 "=" term_0_0 -> c_eq
      | term_0_0

      ?term_22_25 : "\\" name "." term_29_25 -> c_lam
      | term_0_0

      ?term_29_25 : term_22_25
      | term_26_24

      ?term_26_24 : c_app
      | term_0_0

      c_app : term_26_24 " " term_0_0

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
''', start='term', ambiguity='forest')

def graph_of(f):
  # Map each vertex's id to a [str dump of data at that vertex, is vertex an OR node?, list of child ids]
  # In Lark the OR nodes are called SymbolNodes and the AND nodes are called PackedNodes.
  graph = {}
  def go(or_node, f):
    nonlocal graph
    if id(f) in graph: return
    graph[id(f)] = [str(f) + '\n' + str(type(f)), or_node, []] if not hasattr(f, 'children') else [str(type(f)) + '\n' + str(f.s) + '\n' + str(type(f.s)), or_node, list(map(id, f.children))]
    if hasattr(f, 'children'):
      for c in f.children:
        go(not or_node, c)
  go(True, f)
  return graph

def viz(graph):
  entries = []
  mk_color = lambda or_node: 'blue' if or_node else 'black'
  for v, (pretty, or_node, _) in graph.items():
    entries.append(f'v{v} [label={repr(pretty)},color={mk_color(or_node)}]')
  for v, (_, or_node, children) in graph.items():
    for i, c in enumerate(children):
      entries.append(f'v{v} -> v{c} [label={i},color={mk_color(or_node)}]')
  entries = ';\n'.join(entries)
  return f'digraph {{ {entries} }}'

def contract_step(f):
  from lark.parsers.earley_forest import ForestTransformer, SymbolNode, PackedNode, TokenNode
  from lark.grammar import NonTerminal, TOKEN_DEFAULT_PRIORITY
  from lark.lexer import Token
  packed_node_is_singleton = lambda node: (node.left is None, node.right is None) in {(True, False), (False, True)}
  made_change = False
  class T(ForestTransformer):
    def transform_symbol_node(self, node, data):
      contractible = lambda s: s.name.startswith('term')
      can_contract = (
        contractible(node.s)
        and len(data) == 1
        and packed_node_is_singleton(data[0])
      )
      if can_contract:
        nonlocal made_change; made_change = True
        if data[0].left is None: return data[0].right
        else: return data[0].left
      else:
        s = SymbolNode(node.s, node.start, node.end)
        for c in data:
          s.add_family(c.s, c.rule, c.start, c.left, c.right)
        return s
    def transform_intermediate_node(self, node, data):
      can_contract = (
        len(data) == 1
        and packed_node_is_singleton(data[0])
      )
      if can_contract:
        nonlocal made_change; made_change = True
        if data[0].left is None: return data[0].right
        else: return data[0].left
      else:
        s = SymbolNode(node.s, node.start, node.end)
        for c in data:
          s.add_family(c.s, c.rule, c.start, c.left, c.right)
        return s
    def transform_packed_node(self, node, data):
      match data:
        case [p]: return PackedNode(node.parent, node.s, node.rule, node.start, None, p)
        case [p, q]: return PackedNode(node.parent, node.s, node.rule, node.start, p, q)
        case _: assert False
    def transform_token_node(self, node):
      # Hack: node is a Token and there's no way to reconstruct a TokenNode
      # because need access to a TerminalDef but node.type only stores the name
      # of the terminal. Running contraction twice without this would raise an
      # error as Token objects do not have .is_intermediate
      class DummyTerminal:
        name = node.type
        pattern = None
        priority = TOKEN_DEFAULT_PRIORITY
      TokenNode.is_intermediate = False
      return TokenNode(node, DummyTerminal)
  res = T().transform(f)
  return res, made_change

def contract(f):
  while True:
    f, made_change = contract_step(f)
    if not made_change: return f

def parse_tree(f):
  from lark.parsers.earley_forest import TreeForestTransformer
  return TreeForestTransformer(resolve_ambiguity=False).transform(f)

def strip_tokens(f):
  import syntax as S
  class T(Transformer):
    def __default_token__(self, token): return token.value
    def name(self, data): return S.Name(data[0])
    def var(self, data): return S.V(data[0])
    def string(self, data): return Tree('string', data)
    def number(self, data): return Tree('number', data)
    def parens(self, data): return Tree('parens', [data[1]])
    def __default__(self, data, children, meta):
      return Tree(data, [c for c in children if type(c) is not str])
  return T().transform(f)

import pyperclip

# f = term_parser.parse('(((x)))')
# f = term_parser.parse('(((x y)))')
# f = term_parser.parse('(a) (b) (c) (d)')
# f = term_parser.parse('x')
# f = term_parser.parse(r'(\x.x) (\x.x)')
# f = term_parser.parse('a + b + c')
# f = term_parser.parse('(a * b * c)')
f = term_parser.parse('2 + 2 + 2')
f = contract(f)
g = graph_of(f)
pyperclip.copy(viz(g))
print('Graph copied to clipboard')
t = parse_tree(f)
t = strip_tokens(t)
print(t.pretty())