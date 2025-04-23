
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
      return self.transistor.source
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
    #return self.pmos_grid[r][s]
    return self.pmos_grid[r*self.num_sites + s]

  # get cell at (r, s) in nmos grid
  # returns a ResultBlock instance
  def nmos_cell_at(self, r, s):
    return self.nmos_grid[r*self.num_sites + s]


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
    jog_constraint = 2
    max_width = 3

    success = True
    # PMOS
    for r in range(self.result.num_rows):
      for s in range(self.result.num_sites - jog_constraint):
        if self.result.pmos_cell_at(r, s).get_width() > 0:
          prev = max_width - self.result.pmos_cell_at(r, s).get_width()
          has_inc = False
          for i in range(1, jog_constraint+1):
            if has_inc:
              if (max_width - self.result.pmos_cell_at(r, s+i).get_width()) < prev:
                print("ERROR: Jog constraint FAILED at PMOS row", r, "site", s, "with row", r, "site", s+i)
                success = False
            else:
              if (max_width - self.result.pmos_cell_at(r, s+i).get_width()) > prev:
                has_inc = True
            prev = max_width - self.result.pmos_cell_at(r, s+i).get_width()

    # NMOS
    for r in range(self.result.num_rows):
      for s in range(self.result.num_sites - jog_constraint):
        if self.result.nmos_cell_at(r, s).get_width() > 0:
          prev = max_width - self.result.nmos_cell_at(r, s).get_width()
          has_inc = False
          for i in range(1, jog_constraint+1):
            if has_inc:
              if (max_width - self.result.nmos_cell_at(r, s + i).get_width()) < prev:
                print("ERROR: Jog constraint FAILED at NMOS row", r, "site", s, "with row", r, "site", s+i)
                success = False
            else:
              if (max_width - self.result.nmos_cell_at(r, s + i).get_width()) > prev:
                has_inc = True
            prev = max_width - self.result.nmos_cell_at(r, s + i).get_width()

    if success:
      print("Jog constraint PASS")
    return success

  # check whether the diffusion break constraint is met.
  def check_diffusion_break(self):
    diffusion_break_constraint = 2

    success = True

    # PMOS
    for r in range(self.result.num_rows):
      s = 0
      seen_diffusion = False
      while s < self.result.num_sites:
        if self.result.pmos_cell_at(r, s).get_width() == 0:
          i = s+1
          next_used_cell = -1

          while i < self.result.num_sites:
            if self.result.pmos_cell_at(r, i).get_width() > 0:
              next_used_cell = i
              break
            i += 1

          if seen_diffusion and next_used_cell != -1 and (next_used_cell - s) < diffusion_break_constraint:
            print("ERROR: Diffusion break constraint FAILED at PMOS row", r, "site", s, "site", s, "with row", r, "site", next_used_cell, ". Required diffusion break of", diffusion_break_constraint, ", has break of", (next_used_cell - s))
            success = False

          if next_used_cell == -1:
            break
          else:
            s = next_used_cell + 1
        else:
          seen_diffusion = True
          s += 1

    # NMOS
    for r in range(self.result.num_rows):
      s = 0
      seen_diffusion = False
      while s < self.result.num_sites:
        if self.result.nmos_cell_at(r, s).get_width() == 0:
          i = s + 1
          next_used_cell = -1

          while i < self.result.num_sites:
            if self.result.nmos_cell_at(r, i).get_width() > 0:
              next_used_cell = i
              break
            i += 1

          if seen_diffusion and next_used_cell != -1 and (next_used_cell - s) < diffusion_break_constraint:
            print("ERROR: Diffusion break constraint FAILED at NMOS row", r, "site", s, "site", s, "with row", r,
                  "site", next_used_cell, ". Required diffusion break of", diffusion_break_constraint, ", has break of",
                  (next_used_cell - s))
            success = False

          if next_used_cell == -1:
            break
          else:
            s = next_used_cell + 1
        else:
          seen_diffusion = True
          s += 1

    if success:
      print("Diffusion break constraint PASS")
    return success

  def check_widths_sum_up_to_original_width(self):
    pmos_names = {}
    nmos_names = {}
    success = True
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
      if width != pmos_names[name].numfins:
        print("ERROR: Transistor", name, "incorrectly split into", len(all_sub_transistors), "blocks of width", width, "but original width is", pmos_names[name].numfins)
        success = False

    for name in nmos_names :
      all_sub_transistors = []
      for r in range(self.result.num_rows):
        for s in range(self.result.num_sites):
          nmos_block = self.result.nmos_cell_at(r, s)
          if nmos_block.get_transistor_name() == name:
            all_sub_transistors.append(nmos_block)
      # check if all blocks sum up to given width
      width = sum(list(map(lambda x: x.get_width(), all_sub_transistors)))
      if width != nmos_names[name].numfins:
        print("ERROR: Transistor", name, "incorrectly split into", len(all_sub_transistors), "blocks of width", width, "but original width is", nmos_names[name].numfins)
        success = False

    if success:
      print("Width sum PASS")
    return success
    


  def check_source_drain_match(self):
    success = True
    # PMOS
    for r in range(self.result.num_rows):
      for s in range(self.result.num_sites - 1):
        b = self.result.pmos_cell_at(r, s)
        if b.is_empty():
          break

        next = self.result.pmos_cell_at(r, s+1)
        if next.is_empty():
          break

        if b.get_flip_type() == "S-D":
          if next.get_flip_type() == "S-D":
            if b.get_drain() != next.get_source():
              print("ERROR: Net mismatch at row", r, "site", s, "and row", r, "site", s+1, "(Nets", b.get_drain(), next.get_source(),")")
              success = False
          else:
            if b.get_drain() != next.get_drain():
              print("ERROR: Net mismatch at row", r, "site", s, "and row", r, "site", s+1, "(Nets", b.get_drain(), next.get_drain(),")")
              success = False
        else:
          if next.get_flip_type() == "S-D":
            if b.get_source() != next.get_source():
              print("ERROR: Net mismatch at row", r, "site", s, "and row", r, "site", s+1, "(Nets", b.get_source(), next.get_source(),")")
              success = False
          else:
            if b.get_source() != next.get_drain():
              print("ERROR: Net mismatch at row", r, "site", s, "and row", r, "site", s+1, "(Nets", b.get_source(), next.get_drain(),")")
              success = False

    # NMOS
    for r in range(self.result.num_rows):
      for s in range(self.result.num_sites - 1):
        b = self.result.nmos_cell_at(r, s)
        if b.is_empty():
          break

        next = self.result.nmos_cell_at(r, s+1)
        if next.is_empty():
          break

        if b.get_flip_type() == "S-D":
          if next.get_flip_type() == "S-D":
            if b.get_drain() != next.get_source():
              print("ERROR: Net mismatch at row", r, "site", s, "and row", r, "site", s+1, "(Nets", b.get_drain(), next.get_source(),")")
              success = False
          else:
            if b.get_drain() != next.get_drain():
              print("ERROR: Net mismatch at row", r, "site", s, "and row", r, "site", s+1, "(Nets", b.get_drain(), next.get_drain(),")")
              success = False
        else:
          if next.get_flip_type() == "S-D":
            if b.get_source() != next.get_source():
              print("ERROR: Net mismatch at row", r, "site", s, "and row", r, "site", s+1, "(Nets", b.get_source(), next.get_source(),")")
              success = False
          else:
            if b.get_source() != next.get_drain():
              print("ERROR: Net mismatch at row", r, "site", s, "and row", r, "site", s+1, "(Nets", b.get_source(), next.get_drain(),")")
              success = False

    if success:
      print("Net match PASS")
    return success

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
        (f"DS-DS flip type for {mos0}+{mos1}", z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_DS, f_mos1_DS), mos0.src == mos1.drain)),
        # b)
        (f"DS-SD flip type for {mos0}+{mos1}", z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_DS, f_mos1_SD), mos0.src == mos1.src)),
        # c)
        (f"SD-DS flip type for {mos0}+{mos1}", z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_SD, f_mos1_DS), mos0.drain == mos1.drain)),
        # d)
        (f"SD-SD flip type for {mos0}+{mos1}", z3.Implies(z3.And(mos0_c, mos1_c, f_mos0_SD, f_mos1_SD), mos0.drain == mos1.src)), 
        (f"Exactly one flip type for {mos0}", z3.PbEq([(f_mos0_DS, 1), (f_mos0_SD, 1)], 1)),
        (f"Exactly one flip type for {mos1}", z3.PbEq([(f_mos1_DS, 1), (f_mos1_SD, 1)], 1))
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
    # diffusion break constraint 
    if self.diffusion_break <= 1:
      return
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
    print(' Solver: RESULT is: ', r)
    print(' get_model output: ', str(s.model()))
    self.z3model = s.model()
    return (r, s.model())

  def evaluate(self, v):
    return self.z3model.evaluate(v, model_completion = False)

  def parse_flip_type(self, mos): # TODO
    f0 = self.evaluate(self.flip_vars[mos.name][0])
    f1 = self.evaluate(self.flip_vars[mos.name][1])
    if f0 and f1:
      print("ERROR: flip types are both true for mos ", str(mos))
      exit(1)
    else:
      if f0:
        return "D-S"
      else:
        assert f1
        return "S-D"
    

  # m is a Z3model
  def parse_smt_result(self):
    global EMPTY_BLOCK
    result_grid_pmos = []
    result_grid_nmos = []
    for r in range(self.num_rows):
      pmos_row = []
      nmos_row = []
      for s in range(self.num_sites):
        for pmos in self.pmos:
          c_var_pmos_r_s = self.c_vars_p[r][s][pmos.name]
          if self.evaluate(c_var_pmos_r_s):
            # TODO
            flip_type = self.parse_flip_type(pmos)
            block_rs = ResultBlock(pmos.width, flip_type, pmos) # pmos.width = width for placement, not so for splitting.
            pmos_row.append(block_rs)
          else:
            pmos_row.append(EMPTY_BLOCK)
        for nmos in self.nmos:
          c_var_nmos_r_s = self.c_vars_n[r][s][nmos.name]
          if self.evaluate(c_var_nmos_r_s):
            # TODO
            flip_type = self.parse_flip_type(nmos)
            block_rs = ResultBlock(nmos.width, flip_type, nmos) # nmos.width = width for placement, not so for splitting.
            pmos_row.append(block_rs)
          else:
            nmos_row.append(EMPTY_BLOCK)
      result_grid_pmos.append(pmos_row)
      result_grid_nmos.append(nmos_row)
    return Result(self.num_rows, self.num_sites, result_grid_pmos, result_grid_nmos)



s = SATPlacement(
  num_rows = 2,
  num_sites = 2,
  pmos_transistors = [
    Transistor(
      #NAME   DRAIN    GATE      SRC    BLK    PMOS  W   L NFIN
      "p_A", "wire0", "gate_0", "wire1", "blk0", True, 3, 3, 1
    ),
    Transistor(
      "p_B", "wire0", "gate_1", "wire1", "blk1", True, 3, 3, 1
    ),
    Transistor(
      "p_C", "wire1", "gate_2", "wire2", "blk2", True, 3, 3, 1
    ),
    Transistor(
      "p_D", "wire2","gate_3", "wire3", "blk3", True, 3, 3, 1
    )
  ],
   nmos_transistors= [
    Transistor(
      "n_A", "wire0", "gate_0", "wire2", "blk0", False, 3,3,1
    ),
    Transistor(
      "n_B", "wire0", "gate_1", "wire1", "blk0", False, 3,3,1
    )
   ]
   # nmos_transistors = [ 
   # Transistor(
   #   "n_A", "wire0", "gate_0", "wire2", "blk0", False, 3,3,1
   # ), Transistor(
   #   "n_B", "wire1", "gate_1", "wire2", "blk1", False, 3, 3, 1
   # )
  #]
  , diffusion_break = 1 # diffusion break
  )
s.solve()