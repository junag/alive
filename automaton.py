from language import *
from precondition import *
from gen import get_root, CodeGenerator

class MatchingAutomaton:
  def __init__(self, s0):
    self.s0 = s0       # initial state
    self.d = {s0: []}  # transition function
    self.l = {}        # state lables
    self.i = s0 + 1    # next free state
    self.ambg = []     # ambiguities encountered

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

  def has_default_edge(self, s):
    succs = self.d[s]
    for el, succ in succs:
      if (isinstance(el, Value) and el.getName() == "=/=") or el == "=/=":
        return True
    return False

  def inspected_poss(self):
    poss = []
    for s, l in self.l.items():
      if isinstance(l, list):
        poss.append(l)
    return poss

  def declare_matching_vars(self):
    valt = CTypeName('Value')
    poss = []
    vars = []
    for p in self.inspected_poss():
      if p not in poss:
        poss.append(p)
        vars.append(CVariable('*{0}'.format(get_pos_var(p))))
    decl = CDefinition(valt, *vars)
    return decl

  def print_state(self, s, out):
    lab = CLabel('state_{0}'.format(s))
    print(lab.format())
    ne = len(self.d[s])
    if ne and not self.has_default_edge(s):
      ne += 1
    # final state
    if not ne:
      out.write('  printf("matched {0}\\n");\n'.format(self.l[s]))
      out.write('  return nullptr;\n')
    # more than two edges --> use switch
    elif ne > 2:
      self.print_switched_state(s, out)
    # 1 or 2 edges --> use if
    else:
      self.print_if_state(s, out)

  def print_switched_state(self, s, out):
    p = self.l[s]
    a = get_pos_var(p)
    out.write('  switch ({0}->getValueID()) {{\n'.format(a))
    default = None
    for el, succ in self.d[s]:
      if isinstance(el, Instr):
        out.write('  case {0}:\n'.format(el.getOpCodeStr()))
        for i, _ in enumerate(el.operands()):
          ai = get_pos_var(p + [i])
          out.write('    {0} = (cast<Instruction>({1}))->getOperand({2});\n'.format(ai, a, i))
        out.write('    goto state_{0};\n'.format(succ))
      elif is_default_edge(el):
        default = succ
      elif isinstance(el, ConstantVal) or isinstance(el, Input):
        out.write('  case Value::ConstantFirstVal .. Value::ConstantLastVal:\n')
        if isinstance(el, ConstantVal):
          out.write('''    if (match({0}, m_SpecificInt({1})))
      goto state_{2};
    else
      return nullptr;
'''.format(a, el.val, succ))
        else:
          out.write('    goto state_{0};\n'.format(succ))
      else:
        print("unknown edge label: {0}\n".format(el))
        assert(False)
    if default:
      out.write('  default:\n    goto state_{0};\n'.format(default))
    else:
      out.write('  default:\n    return nullptr;\n')
    out.write('  }\n')

  def print_if_state(self, s, out):
    p = self.l[s]
    a = CVariable(get_pos_var(p))
    cond = None
    then_block = []
    else_block = [CReturn(CVariable('nullptr'))]
    for el, succ in self.d[s]:
      gotoSucc = CGoto('state_{0}'.format(succ))
      if is_default_edge(el):
        else_block = [gotoSucc]
      elif isinstance(p, list):
        if isinstance(el, Instr):
          mops = [CFunctionCall('m_Value', CVariable(get_pos_var(p + [i]))) for
                  (i, _) in enumerate(el.operands())]
          cond = el.llvm_matcher(a, *mops)
        elif isinstance(el, ConstantVal):
          # FIXME: specificInt only matches up to 64bit, use APInt and value
          # check instead
          cond = CFunctionCall('match', a, CFunctionCall('m_specificInt',
                                                         CVariable(el.val)))
        elif isinstance(el, Input) and el.isConst():
          cond = el.llvm_matcher(a)
        then_block.append(gotoSucc)
      elif p == "eq":
        cond = CBinExpr('==', CVariable(get_pos_var(el[0])),
                        CVariable(get_pos_var(el[1])))
        then_block.append(gotoSucc)
      elif p == "c":
        # FIXME: names in preconditions are all messed up due to variables not
        # being bound properly
        cg = CodeGenerator()
        el.register_types(cg)
        cond = el.visit_pre(cg)
        then_block.append(gotoSucc)
      else:
        print("unknown edge label: {0}\n".format(el))
        assert(False)
    if cond:
      out.write(str(seq(CIf(cond, then_block, else_block).format())))
    else:
      out.write(str(seq(else_block[0].format())))

  def print_automaton(self, out):
    out.write('Instruction *InstCombiner::runOnInstruction(Instruction *I) {\n')
    out.write('  {0}\n  a = I;\n  goto state_{1};\n\n'.format(str(self.declare_matching_vars().format()), self.s0))
    for s, _ in self.l.items():
      self.print_state(s, out)
    out.write('\n  return nullptr;\n}\n')

  def build_final(self, s, M, pre):

    def compare_pats(p1, p2):
      return get_patr(p2).pattern_matches(get_patr(p1)) or \
          len(get_pat(p1)) > len(get_pat(p2))

    def max_pat(P):
      p = P[0]
      for p1 in P:
        if compare_pats(p1, p):
          p = p1
      return p

    # FIXME: use more sophisticated check of precondition implication
    C = [p for p in M if (linearity_conds(p) | get_pre_conjuncts(p)) <= pre]
    if C and all(any(compare_pats(p1, p) for p1 in C) for p in M):
      self.l[s] = get_name(max_pat(C))
    else:
      p = max_pat(M)
      cs = linearity_conds(p) - pre
      if not cs:
        cs |= get_pre_conjuncts(p) - pre
        self.l[s] = "c"
      else:
        self.l[s] = "eq"
      if not cs:
        if C:
          n = get_name(max_pat(C))
          M1 = [get_name(p) for p in M if not any(compare_pats(p1, p) and
                                                  p1 is not p for p1 in C)]
          if M1 not in self.ambg:
            sys.stderr.write("Warning: could not disambiguate patterns: " +
                             ', '.join(M1) + ". Picking " + n + ".\n")
            self.ambg.append(M1)
          self.l[s] = n
        else:
          assert False, "could not disambiguate patterns " + \
              str([get_name(p) for p in M])
      else:
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
    def compare_pats(p1, p2):
      # return len(get_pat(p1)) >= len(get_pat(p2))
      return get_patr(p2).pattern_matches(get_patr(p1))
    M = [p for p in P if get_patr(p).pattern_matches(e)]
    if M and all(any(compare_pats(p1, p) for p1 in M) for p in P):
      self.build_final(s, M, set())
    else:
      os = e.var_poss()
      if not os:
        assert False, "could not disambiguate patterns " + \
            str([get_name(p) for p in P])
      ofss = [(o, match_templates(P, o)) for o in os]
      o, fss = max(ofss, key=lambda x: len(x[1]))
      self.l[s] = o
      for fs in fss:
        self.build_succs(fs, s, o, e, P, False)

  def build_succs(self, fs, s, o, e, P, b):
    minfs = [f for f in fs if not any(f1.pattern_matches(f) and f1 is not f for
                                      f1 in fs) or f.getName() == "=/="]
    for f in minfs:
      sf = self.new_state_from(s, f)
      P1 = []
      for p in P:
        r = get_patr(p).at_pos(o, True).make_match_template()
        if f.pattern_matches(r) or r.pattern_matches(f):
          P1.append(p)
      succfs = [f1 for f1 in fs if f.pattern_matches(f1) and f1 is not f]
      v = e.at_pos(o)
      if succfs:
        self.l[sf] = o
        self.build_succs(succfs, sf, o, e.replace_at(f, o), P1, True)
      else:
        self.build(sf, e.replace_at(f, o), P1)
      e.replace_at(v, o)
    if b:
      f = Value()
      f.setName("=/=")
      sf = self.new_state_from(s, f)
      r1 = e.at_pos(o)
      P1 = []
      for p in P:
        r = get_patr(p).at_pos(o, True).make_match_template()
        if r.pattern_matches(r1):
          P1.append(p)
      self.build(sf, e, P1)

  def minimize(self):
    def succs_eq(ss, ts):
      if (len(ss) != len(ts)):
        return False
      return set(map(str, ss)) == set(map(str, ts))
    c = True
    while c:
      c = False
      states = list(self.d.items())
      for i, (s, succs) in enumerate(states):
        for s1, succs1 in states[i + 1:]:
          if self.l[s] == self.l[s1] and succs_eq(succs, succs1):
            self.redirect(s, s1)
            del self.d[s]
            del self.l[s]
            c = True
            break

def is_default_edge(el):
  return (isinstance(el, Value) and el.getName() == "=/=") or el == "=/="

def insert_template(f, fss):
  js = []
  for j, fs in enumerate(fss):
    for f1 in fs:
      f1f, ff1 = f.pattern_matches(f1), f1.pattern_matches(f)
      if f1f and ff1:  # variant of pattern already in templates
        return
      elif f1f or ff1:  # found instance or generalization of pattern
        js.append(j)
  fs = [f]
  for j in sorted(list(set(js)), reverse=True):
    fs.extend(fss[j])
    del fss[j]
  fss.append(fs)

def match_templates(opts, o):
  fss = []
  var = False
  for p in opts:
    r = get_patr(p).at_pos(o, True)
    if not isinstance(r, Input) or r.isConst():
      f = r.make_match_template()
      insert_template(f, fss)
    else:
      var = True
  if var:
    f = Value()
    f.setName("=/=")
    fss.append([f])
  return fss

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

def get_pos_var(p, const=False):
  n = 'Ca' if const else 'a'
  return '{0}{1}'.format(n, ''.join([str(i) for i in p]))

def canonicalize_names(opt):
  src = get_patr(opt)
  vs = {}
  for p in src.var_poss(True):
    v = src.at_pos(p)
    n = get_pos_var(p, v.isConst())
    vs[v.getName()] = n
    v.setName(n)
  print(vs)


def build(opts):
  a = MatchingAutomaton(0)
  a.build(0, Input('%_', UnknownType()), opts)
  a.minimize()
  # a.to_dot(sys.stdout)
  # a.print_automaton(sys.stdout)
