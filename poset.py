class Poset:
  def __init__(self):
    self.graph = set()
    self.bots = set()
    self.tops = set()
  def add_bot(self, b):
    self.bots |= {b}
    self.graph |= {(b, z) for (x, y) in self.graph for z in (x, y)}
    return self
  def add_top(self, t):
    self.tops |= {t}
    self.graph |= {(z, t) for (x, y) in self.graph for z in (x, y)}
    return self
  def add(self, x, y):
    if (x, y) in self.graph:
      return
    if y in self.bots:
      return self.add_bot(x)
    if x in self.tops:
      return self.add_top(y)
    self.graph |= {(b, x) for b in self.bots}
    self.graph |= {(b, y) for b in self.bots}
    self.graph |= {(x, t) for t in self.tops}
    self.graph |= {(y, t) for t in self.tops}
    self.graph |= {(x, y)}
    while True:
      done = True
      for (x, y) in tuple(self.graph):
        for (y0, z) in tuple(self.graph):
          if y == y0 and (x, z) not in self.graph:
            done = False
            self.graph |= {(x, z)}
      if done:
        break
    return self
  def le(self, x, y):
    return (x in self.bots) or (y in self.tops) or (x == y) or ((x, y) in self.graph)