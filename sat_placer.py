
"""
  SAT-driven placement
  https://ieeexplore.ieee.org/stamp/stamp.jsp?arnumber=10473978 
"""

import z3 

class SATPlacement(object):

  def __init__(self, num_rows, num_sites, pmos_transistors, nmos_transistors):
    self.constraints = []
    self.variables = []
    self.sharable = [[False if x.gate!=y.gate else True for y in nmos_transistors] for x in pmos_transistors]
    # 1st bit gives direction of pmos in TP-cell, 0 = (D-S), 1 = (S-D) 
    self.flip_types = [0b00, 0b01]
    
    self.pmos = pmos_transistors
    self.nmos = nmos_transistors

    self.num_rows = num_rows
    self.num_sites = num_sites

    self.sharable = {}
    for pmos in self.pmos:
      self.sharable[pmos.name] = {}
      for nmos in self.nmos:
        self.sharable[pmos.name][nmos.name] = (pmos.gate == nmos.gate)

    # XXX todo: partially sharable constraints for D/S, S/D need to be hard-coded

    # variables c_{r, s}^i for each
    self.c_vars_p = {}
    self.c_vars_n = {}
    for r in num_rows:
      self.c_vars_p[r] = {}
      self.c_vars_n[r] = {}
      for s in num_sites:
        pmos_c = z3.Bool(f'c_p_{r}_{s}_{pmos.name}')
        nmos_c = z3.Bool(f'c_n_{r}_{s}_{nmos.name}')
        loc_pb_pmos = []
        loc_pb_nmos = []
        for pmos in self.pmos: 
          self.c_vars_p[r][s][pmos.name] = pmos_c
          loc_pb_pmos.append((pmos, 1)) # weight 1 per term
        for nmos in self.nmos:
          self.c_vars_n[r][s][nmos.name] = nmos_c
          loc_pb_nmos.append((nmos, 1)) # weight 1 per term
        self.constraints.append(z3.PbEq(loc_pb_pmos), 1) # one pmos per (r,s)
        self.constraints.append(z3.PbEq(loc_pb_nmos), 1) # one nmos per (r,s)

        for pmos in self.pmos:
          for nmos in self.nmos:
            # constraint about transistor pairing
            self.constraints.append(z3.Implies(z3.And(pmos_c, nmos_c), self.sharable[pmos][nmos]))
    # pb constraint for each {nmos|pmos} transistor:
    # each pmos is placed in exactly one location
    for mos in self.pmos + self.nmos:
      pbsum = []
      for r in num_rows:
        for s in num_sites:
          if mos.is_pmos:
            pbsum.append((self.c_vars_p[r][s][mos.name], 1)) # weight 1 per term
          else:
            pbsum.append((self.c_vars_n[r][s][mos.name], 1))
      self.constraints.append(z3.PbEq(pbsum, 1))
    # variables f^i_t where t is the flip type, i is a CMOS transistor
    # symmetric for P and N, so we merge them together
    self.flip_vars = {}
    for mos in self.pmos + self.nmos:
      self.flip_vars[mos.name] = list(map(lambda t: z3.Bool(f'f_{mos.anme}_{t}'), self.flip_types))
    
    # pb constraint for flip types: exactly one flip type per transistor
    #TODO: remove this, tautology
    #for mos in self.pmos + self.nmos:
    #  pbsum = []
    #  for f_t in self.flip_vars[mos.name]:
    #    pbsum.append((f_t, 1)) # weight 1 per term
    #  self.constraints.append(z3.PbEq(pbsum, 1))
    
    # constrain which flip types are sharable within each P/N transistor
    # think: there are two flip types for each transistor. This induces 4 cases:
    # a) D-S flip type (0) + D-S flip type (0):
    #   OK if and only if MOS[0].src == MOS[1].drain
    # b) D-S flip type (0) + S-D flip type (1):
    #   OK if and only if MOS[0].src == MOS[1].src
    # c) S-D flip type (1) + D-S flip type (0):
    #   OK if and only if MOS[0].drain == MOS[1].drain
    # d) S-D flip type (1) + S-D flip type (1): 
    #   OK if and only if MOS[0].drain == MOS[1].src
    def neighbor_constraint(r, s, mos0, mos1, mos0_c, mos1_c):
      f_mos0_DS = self.flip_vars[mos0.name][0]
      f_mos0_SD = self.flip_vars[mos0.name][1]
      f_mos1_DS = self.flip_vars[mos1.name][0]
      f_mos1_SD = self.flip_vars[mos1.name][1]
      return [
        # a)
        z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_DS, f_mos1_DS), mos0.src == mos1.drain),
        # b)
        z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_DS, f_mos1_SD), mos0.src == mos1.src),
        # c)
        z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_SD, f_mos1_DS), mos0.drain == mos1.drain),
        # d)
        z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_SD, f_mos1_SD), mos0.drain == mos1.src)
      ]
    for r in range(self.num_rows):
      for s in range(self.num_sites - 1):
        for pmos0 in self.pmos:
          for pmos1 in self.pmos:
            if pmos0.name != pmos1.name:
              pmos0_c = self.c_vars_p[r][s][pmos0.name]
              pmos1_c = self.c_vars_p[r][s][pmos1.name]
              self.constraints += neighbor_constraint(r, s, pmos0, pmos1, pmos0_c, pmos1_c)
        for nmos0 in self.nmos:
          for nmos1 in self.nmos:
            if nmos0.name != nmos1.name:
              nmos0_c = self.c_vars_n[r][s][nmos0.name]
              nmos1_c = self.c_vars_n[r][s][nmos1.name]
              self.constraints += neighbor_constraint(r, s, nmos0, nmos1, nmos0_c, nmos1_c)


  def solve(self):
    s = z3.Solver()
    i = 0
    for x in self.constraints:
      print(' Solver: adding constraint', i, ': ', str(x))
      i = i + 1
    r = s.check()
    print(' Solver: RESULT is: ', r)
    return r
