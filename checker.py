

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
      if width != pmos_names[name].width:
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
      if width != nmos_names[name].width:
        print("ERROR: Transistor", name, "incorrectly split into", len(all_sub_transistors), "blocks of width", width, "but original width is", nmos_names[name].numfins)
        success = False

    if success:
      print("Width sum PASS")
    return success
    


  def check_source_drain_match(self):
    success = True
    print('checking source-drain match...')
    # PMOS
    for r in range(self.result.num_rows):
      for s in range(self.result.num_sites - 1):
        b = self.result.pmos_cell_at(r, s)
        if b.is_empty():
          print(f' -- ({r}, {s}) is empty, skipping')
          continue
        
        next = self.result.pmos_cell_at(r, s+1)
        if next.is_empty():
          print(f' -- ({r}, {s+1}) is empty, skipping')
          continue

        print('SD-match: checking pair ', b.transistor.name, ' + ', next.transistor.name)

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
          continue

        next = self.result.nmos_cell_at(r, s+1)
        if next.is_empty():
          continue

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
