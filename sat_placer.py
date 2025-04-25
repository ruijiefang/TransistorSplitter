
"""
  SAT-driven placement
  https://ieeexplore.ieee.org/stamp/stamp.jsp?arnumber=10473978 
"""
from parser import Transistor 

import z3 

class ResultBlock(object):
  """
    A ResultBlock wraps a Transistor instance by giving it a particular width.
    It could also be empty --- which represents the case where no transistor
    is placed in the particular block.
  """
  # transistor is a instance of parser.Transistor 
  def __init__(self, width, flip_type, transistor=None):
    self.width = width 
    self.transistor = transistor
    self.flip_type = flip_type # either string "S-D" or "D-S"

  # width of the current transistor block, 
  # 
  def get_width(self):
    return self.width

  def get_transistor_name(self):
    if self.transistor != None:
      return self.transistor.name
    else:
      return "EMPTY"

  def get_drain(self):
    if self.transistor != None:
      return self.transistor.drain
    else:
      return ""

  def get_source(self):
    if self.transistor != None:
      return self.transistor.src
    else:
      return ""

  def is_empty(self): # check if this is an empty block
    return self.transistor == None

  def get_transistor(self): # returns None if empty
    return self.transistor
  
  def get_flip_type(self):
    return self.flip_type

# global variable for empty block
EMPTY_BLOCK = ResultBlock(0, "", None)

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
      nmos_grid: similar to above but for NMOS
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
    #return self.pmos_grid[r*self.num_sites + s]

  # get cell at (r, s) in nmos grid
  # returns a ResultBlock instance
  def nmos_cell_at(self, r, s):
    return self.nmos_grid[r][s]
    #return self.nmos_grid[r*self.num_sites + s]

class SATPlacement(object):

  def __init__(self, num_rows, num_sites, pmos_transistors, nmos_transistors, diffusion_break):
    self.constraints = []
    self.variables = []
    self.sharable = [[False if x.gate!=y.gate else True for y in nmos_transistors] for x in pmos_transistors]
    # 1st bit gives direction of pmos in TP-cell, 0 = (D-S), 1 = (S-D) 
    self.flip_types = [0, 1]
    
    self.diffusion_break = diffusion_break

    self.pmos = pmos_transistors
    self.nmos = nmos_transistors

    self.num_rows = num_rows
    self.num_sites = num_sites

    self.sharable = {}
    for pmos in self.pmos:
      self.sharable[pmos.name] = {}
      for nmos in self.nmos:
        self.sharable[pmos.name][nmos.name] = (pmos.gate == nmos.gate)

    # variables c_{r, s}^i for each
    self.c_vars_p = {}
    self.c_vars_n = {}
    for r in range(num_rows):
      self.c_vars_p[r] = {}
      self.c_vars_n[r] = {}
      for s in range(num_sites):
        loc_pb_pmos = []
        loc_pb_nmos = []
        self.c_vars_p[r][s] = {}
        self.c_vars_n[r][s] = {}
        for pmos in self.pmos: 
          pmos_c = z3.Bool(f'c_p_{r}_{s}_{pmos.name}')
          self.c_vars_p[r][s][pmos.name] = pmos_c
          loc_pb_pmos.append((pmos_c, 1)) # weight 1 per term
        for nmos in self.nmos:
          nmos_c = z3.Bool(f'c_n_{r}_{s}_{nmos.name}')
          self.c_vars_n[r][s][nmos.name] = nmos_c
          loc_pb_nmos.append((nmos_c, 1)) # weight 1 per term
        print("loc_pb_pmos: ", loc_pb_pmos)
        self.constraints.append((f"at most one PMOS at ({r}, {s})", z3.PbLe(loc_pb_pmos, 1))) # at most one pmos per (r,s)
        self.constraints.append((f"at most one NMOS at ({r}, {s})", z3.PbLe(loc_pb_nmos, 1))) # at most one nmos per (r,s)

        for pmos in self.pmos:
          for nmos in self.nmos:
            # constraint about transistor pairing
            self.constraints.append((f"pairing between {pmos.name} and {nmos.name}", z3.Implies(z3.And(pmos_c, nmos_c), self.sharable[pmos.name][nmos.name])))
    # pb constraint for each {nmos|pmos} transistor:
    # each pmos is placed in exactly one location
    for mos in self.pmos + self.nmos:
      pbsum = []
      for r in range(num_rows):
        for s in range(num_sites):
          if mos.is_pmos:
            pbsum.append((self.c_vars_p[r][s][mos.name], 1)) # weight 1 per term
          else:
            pbsum.append((self.c_vars_n[r][s][mos.name], 1))
      self.constraints.append((f"{mos.name} in exactly one place", z3.PbEq(pbsum, 1)))
    # variables f^i_t where t is the flip type, i is a CMOS transistor
    # symmetric for P and N, so we merge them together
    self.flip_vars = {}
    for mos in self.pmos + self.nmos:
      self.flip_vars[mos.name] = list(map(lambda t: z3.Bool(f'f_{mos.name}_{t}'), self.flip_types))
        
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
        (f"DS-DS flip type for {mos0.name}+{mos1.name}", z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_DS, f_mos1_DS), mos0.src == mos1.drain)),
        # b)
        (f"DS-SD flip type for {mos0.name}+{mos1.name}", z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_DS, f_mos1_SD), mos0.src == mos1.src)),
        # c)
        (f"SD-DS flip type for {mos0.name}+{mos1.name}", z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_SD, f_mos1_DS), mos0.drain == mos1.drain)),
        # d)
        (f"SD-SD flip type for {mos0.name}+{mos1.name}", z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_SD, f_mos1_SD), mos0.drain == mos1.src)), 
        (f"Exactly one flip type for {mos0.name}", z3.PbEq([(f_mos0_DS, 1), (f_mos0_SD, 1)], 1)),
        (f"Exactly one flip type for {mos1.name}", z3.PbEq([(f_mos1_DS, 1), (f_mos1_SD, 1)], 1))
      ]
    print('adding flip type constraints ... ', len(self.constraints), 'total')
    for r in range(self.num_rows):
      for s in range(self.num_sites - 1):
        for pmos0 in self.pmos:
          for pmos1 in self.pmos:
            if pmos0.name != pmos1.name:
              pmos0_c = self.c_vars_p[r][s][pmos0.name]
              pmos1_c = self.c_vars_p[r][s+1][pmos1.name]
              self.constraints += neighbor_constraint(r, s, pmos0, pmos1, pmos0_c, pmos1_c)
        for nmos0 in self.nmos:
          for nmos1 in self.nmos:
            if nmos0.name != nmos1.name:
              nmos0_c = self.c_vars_n[r][s][nmos0.name]
              nmos1_c = self.c_vars_n[r][s+1][nmos1.name]
              self.constraints += neighbor_constraint(r, s, nmos0, nmos1, nmos0_c, nmos1_c)
    print('done adding flip type constraints..., ', len(self.constraints), ' total')
    #exit(1)
    # diffusion break constraint 
    if self.diffusion_break < 1:
      return
    print('adding diffusion break constraint..., ', len(self.constraints))
    for r in range(self.num_rows):
      for s in range(self.num_sites):
        for pmos in self.pmos:
          conjuncts = []
          c_var_imp = self.c_vars_p[r][s][pmos.name]
          for i in range(self.diffusion_break):
            if s + i < self.num_sites:
              c_var = self.c_vars_p[r][s + i][pmos.name]
              conjuncts.append(z3.Not(c_var))
          self.constraints.append((f"diffusion break for {pmos.name} at ({r}, {s})", z3.Implies(z3.Not(c_var_imp), z3.And(conjuncts))))
        for nmos in self.nmos:
          conjuncts = []
          c_var_imp = self.c_vars_n[r][s][nmos.name]
          for i in range(self.diffusion_break):
            if s + i < self.num_sites:
              c_var = self.c_vars_n[r][s+i][nmos.name]
              conjuncts.append(z3.Not(c_var))
          self.constraints.append((f"diffusion break for {nmos.name} at ({r}, {s})", z3.Implies(z3.Not(c_var_imp), z3.And(conjuncts))))
          
        
  def solve(self):
    s = z3.Solver()
    i = 0
    for x in self.constraints:
      print(' Solver: adding constraint', i, ': ', str(x))
      s.add(x[1])
      i = i + 1
    r = s.check()
    if r == z3.sat:
      print(' Solver: RESULT is: ', r)
      print(' get_model output: ', str(s.model()))
      self.z3model = s.model()
      return (r, s.model())
    else:
      print(' Solver error: RESULT is ', r)
      self.z3model = None 
      return (r, None)

  def evaluate(self, v):
    return self.z3model.evaluate(v) #, model_completion = False)

  def parse_flip_type(self, mos): # TODO
    f0 = self.evaluate(self.flip_vars[mos.name][0])
    f1 = self.evaluate(self.flip_vars[mos.name][1])
    print('flip type 0 value: ', str(f0))
    print('flip type 1 value: ', str(f1))
    if f0 and f1:
      print("ERROR: flip types are both true for mos ", str(mos))
      exit(1)
    else:
      if f0:
        return "D-S"
      else:
        assert f1
        return "S-D"
    
  def print_model(self):
    for key in self.z3model:
      print('[', key, ' = ', self.z3model[key])

  def print_result_grid(self):
    print('--------------- PMOS GRID -----------------------')
    for r in range(self.num_rows):
      for s in range(self.num_sites):
        isempty = True 
        for pmos in self.pmos:
          if self.evaluate(self.c_vars_p[r][s][pmos.name]):
            print(pmos.name, end='\t')
            isempty = False 
            break
        if isempty:
          print('*', end='\t')
      print('')
    print('--------------- NMOS GRID -----------------------')
    for r in range(self.num_rows):
      for s in range(self.num_sites):
        isempty = True
        for nmos in self.nmos:
          if self.evaluate(self.c_vars_n[r][s][nmos.name]):
            print(nmos.name, end='\t')
            isempty = False
            break
        if isempty:
          print('*', end='\t')
      print('')

  def parse_smt_result(self):
    result_grid_pmos = []
    result_grid_nmos = []
    for r in range(self.num_rows):
      pmos_row = []
      nmos_row = []
      for s in range(self.num_sites):
        pmos_placed = False
        nmos_placed = False
        for pmos in self.pmos:
          c_var_pmos_r_s = self.c_vars_p[r][s][pmos.name]
          if self.evaluate(c_var_pmos_r_s):
            if pmos_placed:
              print('ERR: two PMOSes placed at same location ', r, ' : ', s)
            print('placing PMOS cell ', pmos.name, ' at location ', r, ' : ', s)
            flip_type = self.parse_flip_type(pmos)
            print("PMOS Width: ", pmos.width)
            block_rs = ResultBlock(pmos.numfins, flip_type, transistor = pmos) # pmos.width = width for placement, not so for splitting.
            pmos_row.append(block_rs)
            pmos_placed = True
        if not(pmos_placed):
          print('placing empty pmos cell')
          pmos_row.append(EMPTY_BLOCK)
        for nmos in self.nmos:
          c_var_nmos_r_s = self.c_vars_n[r][s][nmos.name]
          if self.evaluate(c_var_nmos_r_s):
            if nmos_placed:
              print('ERR: two NMOSes placed at same location ', r, ' : ', s)
            print('placing NMOS cell ', nmos.name, ' at location ', r, ' : ', s)
            flip_type = self.parse_flip_type(nmos)
            block_rs = ResultBlock(nmos.numfins, flip_type, transistor = nmos) # nmos.width = width for placement, not so for splitting.
            nmos_row.append(block_rs)
            nmos_placed = True
        if not(nmos_placed):
          nmos_row.append(EMPTY_BLOCK)
          print('placing empty nmos cell')
      result_grid_pmos.append(pmos_row)
      result_grid_nmos.append(nmos_row)
    print('PMOS grid: ', result_grid_pmos)
    print('NMOS grid: ', result_grid_nmos)
    return Result(self.num_rows, self.num_sites, result_grid_pmos, result_grid_nmos)

