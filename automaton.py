from language import *
from gen import get_root

class MatchingAutomaton:
  def __init__(self, s0):
    self.s0 = s0
    self.d = {s0: []}
    self.l = {}
    self.i = s0 + 1  # next free state

  def __repr__(self):
    return str((self.l, self.s0, self.d))

  def to_dot(self, out):
    out.write('''digraph dfa {
"" [shape=none]
"" ->''')
    out.write(' "{0}"\n'.format(self.s0))
    for s, l in self.l.items():
      out.write('  "{0}" [label="{1}", shape='.format(s, l))
      if not self.d.get(s):
        out.write('doublecircle]\n')
      else:
        out.write('circle]\n')
    out.write('\n')
    for s, succs in self.d.items():
      for el, succ in succs:
        out.write('  "{0}" -> "{1}" [label="{2}"]\n'.format(s, succ, el))
    out.write('}\n')

  def states(self):
    return list(self.d.keys())

  def sinks(self):
    sinks = []
    for s in self.states():
      if not self.d.get(s):
        sinks.append(s)
    return sinks

  def build(self, s, e, P):
    M = [p for p in P if get_root(p).pattern_matches(e)]
    if M and all(any(len(p1) >= len(p) for p1 in M) for p in P):
      self.l[s] = get_root(max(M, key=lambda p: len(p))).term_repr()
    else:
      os = e.var_poss()
      o = os[len(os) - 1]
      self.l[s] = o
      fs = match_templates(P, o)
      for f in fs:
        sf = self.i
        self.i += 1
        self.d[sf] = []
        self.d[s].append((f, sf))
        v = e.at_pos(o)
        P1 = []
        for p in P:
          r = get_root(p).at_pos(o, True)
          if (isinstance(r, Input) and not r.isConst()) or f.pattern_matches(r):
            P1.append(p)
        self.build(sf, e.replace_at(f, o), P1)
        e.replace_at(v, o)

def match_templates(pats, o):
  fs = []
  var = False
  for p in pats:
    r = get_root(p).at_pos(o, True)
    if not isinstance(r, Input) or r.isConst():
      f = r.make_match_template()
      if not any(f.pattern_matches(f1) for f1 in fs):
        fs.append(f)
    else:
      var = True
  if var:
    f = Value()
    f.setName('=/=')
    fs.append(f)
  return fs

def build(opts):
  pats = []
  for opt in opts:
    name, pre, src_bb, tgt_bb, src, tgt, src_used, tgt_used, tgt_skip = opt
    pats.append(src)

  a = MatchingAutomaton(0)
  a.build(0, Input('%_', UnknownType()), pats)
  a.to_dot(sys.stdout)
