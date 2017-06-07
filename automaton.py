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

  def has_edge(self, s, P):
    succs = self.d[s]
    for el, succ in succs:
      if P(el):
        return True
    return False

  def has_default_edge(self, s):
    return self.has_edge(s,
      lambda el: (isinstance(el, Value) and el.getName() == "=/=") or el == "=/=")

  def has_const_edge(self, s):
    return self.has_edge(s, lambda el: isinstance(el, Input) and el.isConst())

  def has_icmp_edge(self, s):
    return self.has_edge(s, lambda el: isinstance(el, Icmp))

  def inspected_poss(self):
    ps, cps, ips = [], [], []
    for s, l in self.l.items():
      if isinstance(l, list) and l not in ps:
        ps.append(l)
      if self.has_const_edge(s) and l not in cps:
        cps.append(l)
      if self.has_icmp_edge(s) and l not in ips:
        ips.append(l)
    return ps, cps, ips

  def declare_matching_vars(self):
    valt = CTypeName('Value')
    predt = CTypeName('CmpInst::Predicate')
    constt = CTypeName('Constant')
    vs, cs, ps = [], [], []
    vps, cps, ips = self.inspected_poss()
    for p in vps:
      vs.append(CVariable('*{0}'.format(get_pos_var(p))))
    vdecl = CDefinition(valt, *vs) if vs else None
    for p in ips:
      ps.append(CVariable('{0}'.format(get_pos_var(p, pred=True))))
    for p in cps:
      cs.append(CVariable('*{0}'.format(get_pos_var(p, const=True))))
    pdecl = CDefinition(predt, *ps) if ps else None
    cdecl = CDefinition(constt, *cs) if cs else None
    return vdecl, cdecl, pdecl

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
          if isinstance(el, Icmp):
            cond = el.llvm_matcher(a, CVariable(get_pos_var(p, pred=True)), *mops)
          else:
            cond = el.llvm_matcher(a, *mops)
        elif isinstance(el, ConstantVal):
          # FIXME: specificInt only matches up to 64bit, use APInt and value
          # check instead
          cond = CFunctionCall('match', a, CFunctionCall('m_SpecificInt',
                                                         CVariable(el.val)))
        elif isinstance(el, Input) and el.isConst():
          cond = el.llvm_matcher(a, CVariable(get_pos_var(p, const=True)))
        then_block.append(gotoSucc)
      elif p == "eq":
        cond = CBinExpr('==', CVariable(get_pos_var(el[0])),
                        CVariable(get_pos_var(el[1])))
        then_block.append(gotoSucc)
      elif p == "pre":
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
      out.write(str(seq(else_block[0].format(), line)))

  def print_automaton(self, out):
    out.write('Instruction *InstCombiner::runOnInstruction(Instruction *I) {\n')
    for vd in self.declare_matching_vars():
      if vd:
        out.write('  {0}'.format(vd.format()))
    out.write('\n  {0} = I;\n  goto state_{1};\n\n'.format(get_pos_var([]), self.s0))
    for s, _ in self.l.items():
      self.print_state(s, out)
    out.write('\n  return nullptr;\n}\n')

  def build_cond(self, s, M, pre, eq):
    def compare_pats(p1, p2):
      return get_patr(p2).pattern_matches(get_patr(p1)) or \
          len(get_pat(p1)) > len(get_pat(p2))

    def max_pat(P):
      p = P[0]
      for p1 in P:
        if compare_pats(p1, p):
          p = p1
      return p

    C = [p for p in M if all(eq_cond_implied(eq, e) for e in equality_conds(p)) and
         all(pre_cond_implied(pre, c) for c in get_pre_conjuncts(p))]
    if C and all(any(compare_pats(p1, p) for p1 in C) for p in M):
      self.l[s] = get_name(max_pat(C))
    else:
      p = max_pat(M)
      cs = {e for e in equality_conds(p) if not eq_cond_implied(eq, e)}
      if not cs:
        cs = {c for c in get_pre_conjuncts(p) if not pre_cond_implied(pre, c)}
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
        if isinstance(c, BoolPred):
          self.build_pre(s, c, M, pre, eq)
        else:
          self.build_eq(s, c, M, pre, eq)

  def build_eq(self, s, c, M, pre, eq):
    self.l[s] = "eq"
    M1, M2 = M, []
    for p in M:
      if c not in equality_conds(p):
        M2.append(p)
    if M1:
      sc = self.new_state_from(s, (list(list(c)[0]), list(list(c)[1])))
      self.build_cond(sc, M1, pre, insert_eq_cond(eq, c))
    if M2:
      snc = self.new_state_from(s, "=/=")
      self.build_cond(snc, M2, pre, eq)

  def build_pre(self, s, c, M, pre, eq):
    self.l[s] = "pre"
    pre1 = pre | {c}
    pre2 = pre | {c.v if isinstance(c, PredNot) else PredNot(c)}
    M1, M2 = [], []
    for p in M:
      if not pre_conds_unsat(get_pre_conjuncts(p) | pre1):
        M1.append(p)
      if not pre_conds_unsat(get_pre_conjuncts(p) | pre2):
        M2.append(p)
    if M1:
      sc = self.new_state_from(s, c)
      self.build_cond(sc, M1, pre1, eq)
    if M2:
      snc = self.new_state_from(s, "=/=")
      self.build_cond(snc, M2, pre2, eq)

  def build(self, s, P, e, eq):
    def compare_pats(p1, p2):
      # return len(get_pat(p1)) >= len(get_pat(p2))
      return get_patr(p2).pattern_matches(get_patr(p1))
    os = e.var_poss()
    M = [p for p in P if get_patr(p).pattern_matches(e)]
    # do not stop while there are variable positions
    # we need to ensure all variables get bound
    if not os and M and all(any(compare_pats(p1, p) for p1 in M) for p in P):
      self.build_cond(s, M, set(), eq)
    else:
      if not os:
        assert False, "could not disambiguate patterns " + \
            str([get_name(p) for p in P])
      ofss = [(o, match_templates(P, o)) for o in os]
      o, fss = max(ofss, key=lambda x: len(x[1]))
      self.l[s] = o
      for fs in fss:
        self.build_succs(fs, s, o, P, e, eq, False)

  def build_succs(self, fs, s, o, P, e, eq, b):
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
        self.build_succs(succfs, sf, o, P1, e.replace_at(f, o), eq, True)
      else:
        self.build(sf, P1, e.replace_at(f, o), eq)
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
      self.build(sf, P1, e, eq)

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

def equality_conds(opt):
  src = get_patr(opt)
  vs = [(p, src.at_pos(p)) for p in src.var_poss()]
  eqs = set()
  for i, (p, v) in enumerate(vs):
    for (p1, v1) in vs[i + 1:]:
      if v.getName() == v1.getName():
        eqs |= {frozenset({tuple(p), tuple(p1)})}
  return eqs

def get_pre_conjuncts(opt):
  pre = opt[1]
  if isinstance(pre, PredAnd):
    return set(pre.args)
  elif isinstance(pre, TruePred):
    return set()
  else:
    return {pre}

def pre_cond_implied(cs, c):
  # FIXME: use more sophisticated check of precondition implication
  return str(c) in {str(c1) for c1 in cs}

def pre_conds_unsat(cs):
  # FIXME: imeplement proper unsatisfiablity check
  for c in cs:
    for c1 in cs:
      if str(PredNot(c)) == str(c1):
        return True
  return False

def eq_cond_implied(es, e):
  return any(all(p in ps for p in e) for ps in es)

def insert_eq_cond(es, e):
  ms = set()
  js = []
  for j, ps in enumerate(es):
    if any(p in ps for p in e):
      ms |= ps
      js.append(j)
  for j in reversed(js):
    del es[j]
  ms |= e
  es.append(ms)
  return es

def get_pos_var(p, const=False, pred=False):
  n = 'Ca' if const else 'Pa' if pred else 'a'
  return '{0}{1}'.format(n, ''.join([str(i) for i in p]))

def get_pat(opt):
  src = opt[4]
  return src

def get_patr(opt):
  return get_root(get_pat(opt))

def get_name(opt):
  name = opt[0]
  return name

def canonicalize_names(opt):
  src = get_patr(opt)
  names = {}
  for p in src.poss():
    t = src.at_pos(p)
    n = get_pos_var(p, const=t.isConst())
    names[t.getName()] = n
    t.setName(n)

  def upd_dict(d):
    nis = collections.OrderedDict()
    for n, i in d.items():
      if n in names:
        nis[names[n]] = i
      else:
        if isinstance(i, Constant):
          nis[i.getUniqueName()] = i
        else:
          nis[n] = i
    d.clear()
    for n, i in nis.items():
      d[n] = i

  def upd_set(s):
    for n in s:
      if n in names:
        s.remove(n)
        s.add(names[n])

  opt[1].update_names()
  for bb, instrs in opt[2].items():
    upd_dict(instrs)
  for bb, instrs in opt[3].items():
    upd_dict(instrs)
  upd_dict(opt[4])
  get_root(opt[5]).update_names()
  upd_dict(opt[5])
  upd_set(opt[6])
  upd_set(opt[7])
  upd_set(opt[8])

def build(opts):
  for opt in opts:
    print(opt)
    canonicalize_names(opt)
    print(opt)
  # a = MatchingAutomaton(0)
  # a.build(0, opts, Input('%_', UnknownType()), [])
  # a.minimize()
  # a.to_dot(sys.stdout)
  # a.print_automaton(sys.stdout)
