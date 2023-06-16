import networkx as N

class Preorder:
  '''
  A preorder with support for top and bottom elements.
  '''
  def __init__(self):
    self.bots = set()
    self.tops = set()
    # Invariant:
    #   good_closure ==>
    #     closure is reflexive transitive closure of graph
    #     with bot elements self.bots and top elements self.tops
    self.graph = N.DiGraph()
    self.good_closure = True
    self.closure = self.graph
  def elements(self): return self.graph.nodes
  def generator_graph(self):
    g = N.DiGraph(self.graph)
    g.add_nodes_from(self.bots)
    g.add_nodes_from(self.tops)
    if len(self.bots) > 0:
      bot = next(iter(self.bots))
      g.add_edges_from((bot, v) for v in g.nodes)
      g.add_edges_from((v, bot) for v in self.bots)
    if len(self.tops) > 0:
      top = next(iter(self.tops))
      g.add_edges_from((v, top) for v in g.nodes)
      g.add_edges_from((top, v) for v in self.tops)
    return g
  def make_closure(self):
    '''Recompute the transitive closure.'''
    if self.good_closure: return
    g = self.generator_graph()
    self.closure = N.transitive_closure(g, reflexive=True)
    self.good_closure = True
  def touch_closure(self):
    '''Mark transitive closure for recomputation.'''
    self.good_closure = False
  def add_bot(self, b):
    '''Add b as a bottom element.'''
    self.touch_closure()
    self.bots.add(b)
    return self
  def add_top(self, t):
    '''Add t as a top element.'''
    self.touch_closure()
    self.tops.add(t)
    return self
  def add(self, x):
    '''Add x as an element of the poset.'''
    self.touch_closure()
    self.graph.add_node(x)
    return self
  def add_le(self, x, y):
    '''Add the relation x <= y.'''
    self.touch_closure()
    self.graph.add_edge(x, y)
    return self
  def le(self, x, y):
    '''Check whether x <= y in the poset.'''
    self.make_closure()
    return self.closure.has_edge(x, y)
  def ge(self, x, y):
    '''Check whether x >= y in the poset.'''
    return self.le(y, x)

if __name__ == '__main__':
  g = N.DiGraph([(0, 1), (1, 0), (2, 2), (0, 3), (3, 4)])
  print(list(g.successors(0)))
  partition = tuple(N.strongly_connected_components(g))
  print(partition)
  h = N.quotient_graph(g, partition, create_using=N.DiGraph)
  print('h', h.nodes, h.edges)
  h2 = N.DiGraph((u, w) for (u, v) in h.edges for (v_, w) in h.edges if v == v_)
  print('h2', h2.nodes, h2.edges)
  h.remove_edges_from(h2.edges)
  print('h-h2', h.nodes, h.edges)
