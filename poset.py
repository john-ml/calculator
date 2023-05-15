import networkx as N

class Poset:
  def __init__(self):
    self.bots = set()
    self.tops = set()
    # Invariant:
    #   up_to_date ==>
    #   closure is Kleene closure of graph
    #   with bot elements self.bots ∪ {'bot'} and top elements self.tops ∪ {'top'}
    self.graph = N.DiGraph()
    self.closure = self.graph
    self.up_to_date = True
  def update(self):
    if self.up_to_date: return
    self.closure = N.DiGraph(self.graph)
    self.closure.add_nodes_from(['bot', 'top'])
    self.closure.add_edges_from(('bot', v) for v in self.closure.nodes)
    self.closure.add_edges_from((v, 'top') for v in self.closure.nodes)
    self.closure.add_edges_from((v, 'bot') for v in self.bots)
    self.closure.add_edges_from(('top', v) for v in self.tops)
    self.closure = N.transitive_closure(self.closure, reflexive=True)
    self.up_to_date = True
  def add_bot(self, b):
    self.bots.add(b)
    self.up_to_date = False
    return self
  def add_top(self, t):
    self.tops.add(t)
    self.up_to_date = False
    return self
  def add(self, x, y):
    self.graph.add_edge(x, y)
    self.up_to_date = False
    return self
  def le(self, x, y):
    self.update()
    return (x in self.bots) or (y in self.tops) or (x == y) or self.closure.has_edge(x, y)