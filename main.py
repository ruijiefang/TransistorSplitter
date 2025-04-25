from sat_placer import SATPlacement 
from parser import Transistor, print_cdl, absolute, parse_cdl
from checker import Checker 

from sys import argv 

def test1():
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
  r = s.parse_smt_result()
  c = Checker(r)
  c.check_source_drain_match()
  c.check_diffusion_break()
  c.check_jog()
  c.check_widths_sum_up_to_original_width()


def tryparser():
  if len(argv) != 2:
    raise ValueError("tryparser(): malformed argv string: " + "\t".join(argv))
  file = absolute(argv[1])
  print(" * CDL parser: parsing input file ", file)
  blocks = parse_cdl(file)
  print(" * CDL parser: parsing done. ")
  print_cdl(blocks)
  # print("******************** trying pairing for each transistor block ***************")
  # for block in blocks:
  #  print("*** pairing block ", block.name)
  #  pairer = TransistorPairer(block)
  #  result = pairer.pairing()
  #  print('* >>> pairing success')
  #  pairs = result.pmos_nmos_pairs()
  #  for (pmos, nmos) in pairs:
  #    print("* PAIR: ", pmos.name, " ; ", nmos.name)
  # print("********")
  print('trying to generate a valid placement on grid')
  for block in blocks:
    pmos = list(filter(lambda x: x.is_pmos, block.transistors))
    nmos = list(filter(lambda x: not(x.is_pmos), block.transistors))
    placer = SATPlacement(1, 30, pmos, nmos, diffusion_break=1)
    print('placement result: ', placer.solve())
    placer.print_model()
    r = placer.parse_smt_result()
    c = Checker(r)
    c.check_source_drain_match()
    c.check_diffusion_break()
    c.check_jog()
    c.check_widths_sum_up_to_original_width()

    

if __name__ == "__main__":
  tryparser()
