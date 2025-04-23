
"""
  SAT-driven placement
  https://ieeexplore.ieee.org/stamp/stamp.jsp?arnumber=10473978 
"""

import z3 

class ResultBlock(object):
  """
    A ResultBlock wraps a Transistor instance by giving it a particular width.
    It could also be empty --- which represents the case where no transistor
    is placed in the particular block.
  """
  # transistor is a instance of parser.Transistor 
  def __init__(self, width, transistor=None):
    self.width = width 
    self.transistor = transistor

  # width of the current transistor block, 
  # 
  def get_width(self):
    return self.width

  def get_transistor_name(self):
    if self.transistor != None:
      return self.transistor.name
    else:
      return "EMPTY"

  def is_empty(self): # check if this is an empty block
    return self.transistor == None

  def get_transistor(self): # returns None if empty
    return self.transistor


class Result(object):
  """
    Represents a result of a SAT-based transistor placer
    The result is a grid of size num_rows x num_sites.
    One grid for all pMOS, one grid for all nMOS.
    Each row of the grid is a list of transistors, each of possibly different widths.
    If several transistors share diffusion, they are represent individually, for instance,
    +-----+
    |  |  |
    |  +--+
    |  |
    +--+
    This could be the folding result of one big transistor, but we represent them as two
    separate rectangles on the grid.

      num_rows: integer, representing number of rows
      num_sites: integer, representing number of sites
      pmos_grid: list of list of ResultBlock objects, representing the PMOS grid.
      nmos: grid: similar to above but for NMOS
  """

  def __init__(self, num_rows, num_sites, pmos_grid, nmos_grid):
    self.num_rows = num_rows
    self.num_sites = num_sites
    self.pmos_grid = pmos_grid
    self.nmos_grid = nmos_grid

  # get cell at (r, s) in pmos grid
  # returns a ResultBlock instance 
  def pmos_cell_at(self, r, s):
    return self.pmos_grid[r][s]

  # get cell at (r, s) in nmos grid
  # returns a ResultBlock instance
  def nmos_cell_at(self, r, s):
    return self.nmos_grid[r][s]


class Checker(object):
  """
    A sample checker class to check legality of placement results.
    `result` denotes a Result instance outputted by the placer/splitter.
  """
  def __init__(self, result):
    self.result = result

  # check whether the jog constraint is met.
  """
  +   +   +   +
  |   |   |   |
  |   +---+   |
  |   |jog|   |
  +---+   +---+
  """
  def check_jog(self):
    pass

  # check whether the diffusion break constraint is met.
  def check_diffusion_break(self):
    pass

  def check_widths_sum_up_to_original_width(self):
    pmos_names = {}
    nmos_names = {}
    for r in range(self.result.num_rows):
      for s in range(self.result.num_sites):
        pmos = self.result.pmos_cell_at(r, s)        
        nmos = self.result.nmos_cell_at(r, s)
        if pmos.get_transistor_name() != "EMPTY":
          pmos_names[pmos.get_transistor_name()] = pmos.get_transistor()
        if nmos.get_transistor_name() != "EMPTY":
          nmos_names[nmos.get_transistor_name()] = nmos.get_transistor()
    # check whether each pmos/nmos sub-transistors have width that sum
    # up to the original one.
    for name in pmos_names :
      all_sub_transistors = []
      for r in range(self.result.num_rows):
        for s in range(self.result.num_sites):
          pmos_block = self.result.pmos_cell_at(r, s)
          if pmos_block.get_transistor_name() == name:
            all_sub_transistors.append(pmos_block)
      # check if all blocks sum up to given width
      width = sum(list(map(lambda x: x.get_width(), all_sub_transistors)))
      if width != pmos_names[pmos].width:
        print("ERROR: transistor ", name, " incorrectly split into ", len(all_sub_transistors), " blocks of width ", width, " but original width is ", pmos_names.width)
    # TODO: do the same for the NMOS grid
    


  def check_source_drain_match(self):
    pass


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
