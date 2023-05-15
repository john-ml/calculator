import networkx as N

class Poset:
  '''
  A poset with support for top and bottom elements.
  Maintains a DAG of SCC-equivalence-classes, called the 'skeleton', whose
  transitive closure is the poset. For example, if have the poset
    a <= b
    b <= a
    a <= c <= d
    a <= d
  this class maintains the dag
    {a, b} <= {c} <= {d}
  where a and b are identified and the transitive inequality a <= d is deleted.
  '''
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
    '''Recompute the transitive closure.'''
    if self.good_closure: return
    self.closure = N.DiGraph(self.graph)
    if len(self.bots) > 0:
      bot = next(iter(self.bots))
      self.closure.add_edges_from([(bot, v) for v in self.closure.nodes])
      self.closure.add_edges_from((v, bot) for v in self.bots)
    if len(self.tops) > 0:
      top = next(iter(self.tops))
      self.closure.add_edges_from([(v, top) for v in self.closure.nodes])
      self.closure.add_edges_from((top, v) for v in self.tops)
    self.closure = N.transitive_closure(self.closure, reflexive=True)
    self.good_closure = True
  def make_skeleton(self):
    '''Recompute the skeleton.'''
    if self.good_skeleton: return
    self.make_closure()
    # Skeleton is computed in two steps:
    #   1. Take the transitive closure and contract SCCs into points.
    #      This also gets rid of any self-loops, so the result is a dag G.
    #      G is transitively closed, so x->y in G iff there is a nontrivial path from x to y in G.
    #   3. Skeleton is G - G^2 where G^2 consists of edges corresponding to paths of length > 1 in G.
    #      Intuitively this leaves only paths x->y in G that are not made from paths of length > 1.
    partition = tuple(N.strongly_connected_components(self.closure))
    self.partition = {x: eclass for eclass in partition for x in eclass}
    g = N.quotient_graph(self.closure, partition, create_using=N.DiGraph)
    g2 = N.DiGraph((u, w) for (u, v) in g.edges for (v_, w) in g.edges if v == v_)
    g.remove_edges_from(g2.edges)
    self.skeleton = g
    self.good_skeleton = True
  def touch_closure(self):
    '''Mark transitive closure for recomputation.'''
    self.good_closure = False
    self.good_skeleton = False
  def touch_skeleton(self):
    '''Mark skeleton for recomputation.'''
    self.good_skeleton = False
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
  def canon(self, x):
    '''
    Return the SCC-equivalence-class containing x, represented as a frozenset()
    of poset elements.
    '''
    self.make_closure()
    return self.partition[x]
  def succs(self, eclass):
    '''
    Given an SCC-equivalence-class, represented as a frozenset() of poset
    elements, return its successors in the skeleton.
    '''
    self.make_closure()
    return self.skeleton.successors(eclass)

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
