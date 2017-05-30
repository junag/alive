from language import *
from precondition import *
from gen import get_root

class MatchingAutomaton:
  def __init__(self, s0):
    self.s0 = s0       # initial state
    self.d = {s0: []}  # transition function
    self.l = {}        # state lables
    self.i = s0 + 1    # next free state

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

  def redirect(self, s1, s2):
    for s, succs in self.d.items():
      for i, (el, succ) in enumerate(succs):
        if succ == s1:
          succs[i] = (el, s2)

  def new_state_from(self, s, l):
    sl = self.i
    self.i += 1
    self.d[sl] = []
    self.d[s].append((l, sl))
    return sl

  def build_final(self, s, M, pre):
    C = [p for p in M if (linearity_conds(p) | get_pre_conjuncts(p)) <= pre]
    # print('\npre: ' + str(pre))
    # print('C: ' + str([str(get_patr(p).term_repr()) for p in C]))
    # print('M: ' + str([str(get_patr(p).term_repr()) for p in M]))
    if C and all(any(len(get_pat(p1)) >= len(get_pat(p)) for p1 in C) for p in M):
      self.l[s] = get_name(max(C, key=lambda p: len(get_pat(p))))
    else:
      p = max(M, key=lambda p: len(get_pat(p)))
      cs = linearity_conds(p) - pre
      if not cs:
        cs |= get_pre_conjuncts(p) - pre
        self.l[s] = "c"
      else:
        self.l[s] = "eq"
      c = cs.pop()
      cl = (list(c[0]), list(c[1])) if not isinstance(c, BoolPred) else c
      sc = self.new_state_from(s, cl)
      self.build_final(sc, M, pre | {c})
      M1 = []
      for p in M:
        if c not in linearity_conds(p) and c not in get_pre_conjuncts(p):
          M1.append(p)
      if M1:
        snc = self.new_state_from(s, "=/=")
        self.build_final(snc, M1, pre)

  def build(self, s, e, P):
    M = [p for p in P if get_patr(p).pattern_matches(e)]
    # print('\ne: ' + str(e.term_repr()))
    # print('M: ' + str([str(get_patr(p).term_repr()) for p in M]))
    # print('P: ' + str([str(get_patr(p).term_repr()) for p in P]))
    if M and all(any(len(get_pat(p1)) >= len(get_pat(p)) for p1 in M) for p in P):
      self.build_final(s, M, set())
    else:
      os = e.var_poss()
      # if we end up here without any variables positions to test that must mean
      # that there is a variable constant that needs to be specialized for a pattern to match
      if not os:
        os = e.var_poss(True)
      ofss = [(o, match_templates(P, o, e)) for o in os]
      o, fs = max(ofss, key=lambda x: len(x[1]))
      self.l[s] = o
      for f in fs:
        sf = self.new_state_from(s, f)
        v = e.at_pos(o)
        P1 = []
        for p in P:
          r = get_patr(p).at_pos(o, True)
          if (isinstance(r, Input) and not r.isConst()) or f.pattern_matches(r):
            P1.append(p)
        self.build(sf, e.replace_at(f, o), P1)
        e.replace_at(v, o)

  def minimize(self):
    c = True
    while c:
      c = False
      states = list(self.d.items())
      for i, (s, succs) in enumerate(states):
        for s1, succs1 in states[i + 1:]:
          if self.l[s] == self.l[s1] and succs == succs1:
            self.redirect(s, s1)
            del self.d[s]
            del self.l[s]
            c = True
            break

def match_templates(opts, o, e):
  fs = []
  var = False
  c = e.at_pos(o).isConst()
  for p in opts:
    r = get_patr(p).at_pos(o, True)
    if not isinstance(r, Input) or r.isConst():
      # special case: if e|_o is a constant we only look for concrete values
      if not c or r.isConst():
        f = r.make_match_template()
        if not any(f.pattern_matches(f1) for f1 in fs):
          fs.append(f)
    else:
      var = True
  # only consider var positions if there is at least one other symbol to test
  if fs and var:
    f = Value()
    f.setName('=/=')
    fs.append(f)
  return fs

def linearity_conds(opt):
  src = get_patr(opt)
  vs = [(p, src.at_pos(p)) for p in src.var_poss()]
  eqs = set()
  for i, (p, v) in enumerate(vs):
    for (p1, v1) in vs[i + 1:]:
      if v.getName() == v1.getName():
        eqs |= {(tuple(p), tuple(p1))}
  return eqs

def get_pat(opt):
  _, _, _, _, src, _, _, _, _ = opt
  return src

def get_patr(opt):
  return get_root(get_pat(opt))

def get_name(opt):
  name, _, _, _, _, _, _, _, _ = opt
  return name

def get_pre_conjuncts(opt):
  _, pre, _, _, _, _, _, _, _ = opt
  if isinstance(pre, PredAnd):
    return set(pre.args)
  elif isinstance(pre, TruePred):
    return set()
  else:
    return {pre}

def build(opts):
  a = MatchingAutomaton(0)
  a.build(0, Input('%_', UnknownType()), opts)
  a.minimize()
  a.to_dot(sys.stdout)
