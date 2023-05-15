import networkx as N

# A poset with top and bottom elements 'bot' and 'top'
class Poset:
  def __init__(self):
    self.bots = set()
    self.tops = set()
    # Invariant:
    #   good_closure ==>
    #     closure is Kleene closure of graph
    #     with bot elements self.bots ∪ {'bot'} and top elements self.tops ∪ {'top'}
    #   good_skeleton ==>
    #     partition[v] gives SCC-equivalence-class of v in closure
    #     and skeleton gives DAG of SCC-equivalence-classes with no transitive edges
    #   good_skeleton ==> good_closure
    self.graph = N.DiGraph()
    self.good_closure = True
    self.closure = self.graph
    self.good_skeleton = True
    self.partition = []
    self.skeleton = N.DiGraph()
  def make_closure(self):
    if self.good_closure: return
    self.closure = N.DiGraph(self.graph)
    self.closure.add_edges_from([('bot', v) for v in self.closure.nodes])
    self.closure.add_edges_from([(v, 'top') for v in self.closure.nodes])
    self.closure.add_edges_from((v, 'bot') for v in self.bots)
    self.closure.add_edges_from(('top', v) for v in self.tops)
    self.closure = N.transitive_closure(self.closure, reflexive=True)
    self.good_closure = True
  def make_skeleton(self):
    if self.good_skeleton: return
    self.make_closure()
    partition = tuple(N.strongly_connected_components(self.closure))
    self.partition = {x: eclass for eclass in partition for x in eclass}
    g = N.quotient_graph(self.closure, partition, create_using=N.DiGraph)
    g2 = N.DiGraph((u, w) for (u, v) in g.edges for (v_, w) in g.edges if v == v_)
    g.remove_edges_from(g2.edges)
    self.skeleton = g
    self.good_skeleton = True
  def touch_closure(self):
    self.good_closure = False
    self.good_skeleton = False
  def touch_skeleton(self):
    self.good_skeleton = False
  def add_bot(self, b):
    self.touch_closure()
    self.bots.add(b)
    return self
  def add_top(self, t):
    self.touch_closure()
    self.tops.add(t)
    return self
  def add(self, x):
    self.touch_closure()
    self.graph.add_node(x)
    return self
  def add_le(self, x, y):
    self.touch_closure()
    self.graph.add_edge(x, y)
    return self
  def le(self, x, y):
    self.make_closure()
    return self.closure.has_edge(x, y)
  def canon(self, x):
    self.make_closure()
    return self.partition[x]
  def succs(self, x):
    self.make_closure()
    return self.skeleton.successors(x)

if __name__ == '__main__':
  g = N.DiGraph([(0, 1), (1, 0), (2, 2), (0, 3), (3, 4)])
  partition = tuple(N.strongly_connected_components(g))
  print(partition)
  h = N.quotient_graph(g, partition, create_using=N.DiGraph)
  print('h', h.nodes, h.edges)
  h2 = N.DiGraph((u, w) for (u, v) in h.edges for (v_, w) in h.edges if v == v_)
  print('h2', h2.nodes, h2.edges)
  h.remove_edges_from(h2.edges)
  print('h-h2', h.nodes, h.edges)
