from language import *
from precondition import *
from gen import get_root, CodeGenerator, minimal_type_constraints

class MatchingAutomaton:
  def __init__(self, s0):
    self.s0 = s0        # initial state
    self.d = {s0: []}   # transition function
    self.l = {}         # state lables
    self.i = s0 + 1     # next free state
    self.ambg = []      # ambiguities encountered
    self.eq_conds = {}  # pointer equality conditions
    self.cg = CodeGenerator()

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
    if isinstance(l, (Instr, Constant, BoolPred)):
      l.register_types(self.cg)
    self.d[s].append((l, sl))
    return sl

  def has_edge(self, s, P):
    succs = self.d[s]
    for el, succ in succs:
      if P(el):
        return True
    return False

  def has_default_edge(self, s):
    return self.has_edge(s, lambda el: is_default_edge(el))

  def has_const_edge(self, s):
    return self.has_edge(s, lambda el: isinstance(el, Input) and el.isConst())

  def has_icmp_edge(self, s):
    return self.has_edge(s, lambda el: isinstance(el, Icmp))

  def inspected_poss(self):
    ps, cps, ips = [], [], []
    for s, l in self.l.items():
      if isinstance(l, list) and l not in ps:
        ps.append(l)
      for el, _ in self.d[s]:
        if isinstance(el, tuple):
          for l in el:
            if l not in ps:
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

  def llvm_type_cond(self, el, v):
    req = self.cg.required[el]
    gua = self.cg.guaranteed[el]
    ty_exp = v.arr("getType", [])
    c = minimal_type_constraints(ty_exp, req, gua)
    if c:
      return CBinExpr.reduce('&&', c)

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
        assert False, "unknown edge label: {0}\n".format(el)
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
          type_cond = self.llvm_type_cond(el, a)
          if type_cond:
            cond = CBinExpr('&&', cond, type_cond)
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
        cond = el.visit_pre(self.cg)
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
    out.write('\n  {0} = I;'.format(get_pos_var([])))
    out.write('\n  goto state_{0};\n\n'.format(self.s0))
    for s, _ in self.l.items():
      self.print_state(s, out)
    out.write('\n  return nullptr;\n}\n')

  def make_eq_conds(self, opts):
    def econds(opt):
      src = get_patr(opt)
      ss = [(p, src.at_pos(p)) for p in src.poss()]
      es = []
      for i, (p, s) in enumerate(ss):
        for (p1, s1) in ss[i + 1:]:
          if s.getUniqueName() == s1.getUniqueName():
            es.append(frozenset({tuple(p), tuple(p1)}))
      return es
    for opt in opts:
      self.eq_conds[get_name(opt)] = econds(opt)

  def equality_conds(self, opt):
    return self.eq_conds[get_name(opt)]

  def equality_conds_at_pos(self, o, P):
    es = []
    for conds in [self.eq_conds[get_name(p)] for p in P]:
      for cond in conds:
        if tuple(o) in cond:
          es.append(cond)
    return es

  def match_templates(self, P, o):
    fss = []
    var = False
    for p in P:
      r = get_patr(p).at_pos(list(o), True)
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

  def build_cond(self, s, M, pre):
    def compare_pats(p1, p2):
      # a pattern p1 is larger than p2 if it is an instance of p2 and either
      # they are not variants of each other or p1 has more specific
      # preconditions and equality constraints
      # FIXME: also check size, i.e., len(get_pat(p1)) > len(get_pat(p2))) ?
      return (get_patr(p2).pattern_matches(get_patr(p1)) and
              (not get_patr(p1).pattern_matches(get_patr(p2)) or
               (all(pre_cond_implied(get_pre_conjuncts(p1), c) for c in get_pre_conjuncts(p2)) and
                all(e in self.equality_conds(p1) for e in self.equality_conds(p2)))))

    def max_pats(P):
      mp = []
      for p in P:
        if not any(p1 is not p and compare_pats(p1, p) for p1 in P):
          mp.append(p)
      return mp
    C = [p for p in M if all(pre_cond_implied(pre, c) for c in get_pre_conjuncts(p))]
    mps = max_pats(C)
    # if there is a unique maximal pattern pick it
    if len(mps) == 1 and all(any(compare_pats(p1, p) for p1 in C) for p in M):
      self.l[s] = get_name(mps[0])
    # otherwise disambiguate further
    else:
      cs = []
      for p in M:
        cs.extend([c for c in get_pre_conjuncts(p) if not pre_cond_implied(pre, c)])
      if not cs:
        if mps:
          n = get_name(mps[0])
          ns = [get_name(p) for p in mps]
          if ns not in self.ambg:
            sys.stderr.write("Warning: could not disambiguate patterns: " +
                             ', '.join(ns) + ". Picking " + n + ".\n")
            self.ambg.append(ns)
          self.l[s] = n
        else:
          assert False, "could not disambiguate patterns " + \
              str([get_name(p) for p in M])
      else:
        # FIXME: choose most discriminating precondition
        c = cs.pop()
        self.build_pre(s, c, M, pre)

  def build_pre(self, s, c, M, pre):
    self.l[s] = "pre"
    pre1 = pre | {c}
    # FIXME: better negation propagation?
    pre2 = pre | {c.v if isinstance(c, PredNot) else PredNot(c)}
    M1, M2 = [], []
    for p in M:
      if not pre_conds_unsat(get_pre_conjuncts(p) | pre1):
        M1.append(p)
      if not pre_conds_unsat(get_pre_conjuncts(p) | pre2):
        M2.append(p)
    if M1:
      sc = self.new_state_from(s, c)
      self.build_cond(sc, M1, pre1)
    if M2:
      snc = self.new_state_from(s, "=/=")
      self.build_cond(snc, M2, pre2)

  def build_eq(self, s, c, P, e, eq, o, eqp):
    self.l[s] = "eq"
    P1, P2 = [], []
    v = e.at_pos(eqp)
    for p in P:
      if c not in self.equality_conds(p):
        P2.append(p)
      r = get_patr(p).at_pos(o, True)
      if not eq_conds_unsat(self.equality_conds(p) + [c]):
        if r.pmatches(v, e):  # or (v.pattern_matches(r) and not v.isConst()):
          P1.append(p)
    assert P1 or P2
    if P1:
      sc = self.new_state_from(s, (list(list(c)[0]), list(list(c)[1])))
      v1 = e.at_pos(o)
      eq1 = copy.copy(eq)
      eqv = Value()
      eqv.setName(eqp)
      self.build(sc, P1, e.replace_at(eqv, o), insert_eq_cond(eq1, c))
      e.replace_at(v1, o)
    if P2:
      snc = self.new_state_from(s, "=/=")
      self.build(snc, P2, e, eq)

  def build(self, s, P, e, eq):
    def compare_pats(p1, p2):
      return get_patr(p2).pattern_matches(get_patr(p1))
    os = e.var_poss()
    M = [p for p in P if get_patr(p).pattern_matches(e)]
    # do not stop while there are variable positions in e
    # we need to ensure all variables get bound and check all equality constraints
    if not os and M and all(any(compare_pats(p1, p) for p1 in M) for p in P):
      self.build_cond(s, M, set())
    else:
      if not os:
        print(str([get_name(p) for p in M]))
        print(e.term_repr())
        assert False, "could not disambiguate patterns " + \
            str([get_name(p) for p in P])
      ofss = [(o, self.match_templates(P, o)) for o in os]
      # the current equality constraint checking requires that one of the
      # constraint branches is fully explored
      # FIXME: for now this is done by enforcing depth first search
      o, fss = ofss[0]  # max(ofss, key=lambda x: len(x[1]))
      es = {e for e in self.equality_conds_at_pos(o, P) if not eq_cond_implied(eq, e)}
      eqp = None
      # if there is an equality constraint for this position and the other
      # position has already been visitied check the constraint now
      while es and not eqp:
        c = es.pop()
        p1, p2 = list(list(c)[0]), list(list(c)[1])
        v1, v2 = e.at_pos(p1, True), e.at_pos(p2, True)
        if not v1.getName() == "%_":
          eqp = p1
        elif not v2.getName() == "%_":
          eqp = p2
      if eqp:
        self.build_eq(s, c, P, e, eq, o, eqp)
      else:
        self.l[s] = o
        for fs in fss:
          self.build_succs(fs, s, o, P, e, eq, False)

  def build_succs(self, fs, s, o, P, e, eq, b):
    minfs = [f for f in fs if not any(f1.pattern_matches(f) and f1 is not f for
                                      f1 in fs) or f.getName() == "=/="]
    for f in minfs:
      P1 = []
      for p in P:
        r = get_patr(p).at_pos(o, True).make_match_template()
        if f.pattern_matches(r) or r.pattern_matches(f):
          P1.append(p)
      if P1:
        sf = self.new_state_from(s, f)
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
      r1 = e.at_pos(o)
      P1 = []
      for p in P:
        r = get_patr(p).at_pos(o, True).make_match_template()
        if r.pattern_matches(r1):
          P1.append(p)
      if P1:
        sf = self.new_state_from(s, f)
        self.build(sf, P1, e, eq)

  # FIXME: improve performance
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

def minimal_equality_conds(opt):
  src = get_patr(opt)
  nps = {src.getUniqueName(): {tuple([])}}
  wl = [src]
  while wl:
    s = wl.pop()
    if isinstance(s, Instr):
      p = list(nps[s.getUniqueName()])[0]
      for i, si in enumerate(s.operands()):
        n = si.getUniqueName()
        if n not in nps:
          nps[n] = set()
          wl.append(si)
        nps[n] |= {(tuple(list(p) + [i]))}
  es = []
  for n, ps in nps.items():
    lps = list(ps)
    while len(lps) > 1:
      p = lps.pop()
      es.append(frozenset({p, lps[0]}))
  return es

def pos_above(p1, p2):
  return p2[:len(p1)] == p1

def pos_sabove(p1, p2):
  return pos_above(p1, p2) and not p1 == p2

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

def eq_conds_unsat(es):
  us = []
  for e in es:
    insert_eq_cond(us, e)
  for eqs in us:
    if any(any(pos_sabove(p1, p2) for p1 in eqs) for p2 in eqs):
      return True
  return False

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
  es.append(frozenset(ms))
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

# FIXME: canonicalizing names like below destroys optimization verification,
# because inputs no longer start with '%'
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
    canonicalize_names(opt)
  a = MatchingAutomaton(0)
  a.make_eq_conds(opts)
  a.build(0, opts, Input('%_', UnknownType()), [])
  a.minimize()
  a.to_dot(sys.stdout)
  # a.print_automaton(sys.stdout)
