from sat_placer import SATPlacement 
from parser import Transistor, print_cdl, absolute, parse_cdl
from checker import Checker 

import argparse 


def run_test(num_rows, num_sites, pmos, nmos, diffbreak):
    print('run_test: running a test... num_rows = ', num_rows, 
          ' num_sites = ', num_sites, 
          ' #pmos=', len(pmos), 
          ' #nmos=', len(nmos), 
          ' diffusion break=', diffbreak)
    s = SATPlacement(num_rows, num_sites, pmos_transistors=pmos, nmos_transistors=nmos, diffusion_break=diffbreak)
    s.solve()
    if s.z3model != None:
        r = s.parse_smt_result()
        s.print_result_grid()
        c = Checker(r)
        c.check_source_drain_match()
        c.check_diffusion_break()
        c.check_jog()
        c.check_widths_sum_up_to_original_width()
    else:
       print('run_test: UNSAT. exiting...')



def test1():
  run_test(2, 2, 
    pmos= [
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
    nmos= [
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
    , diffbreak= 1 # diffusion break
    )

def test2():
   run_test(1, 3, 
            pmos = [
               Transistor('PMOS_A', 'wire0', 'gate0', 'wire1', 'blk0', True, 3, 3, 1),
               Transistor('PMOS_B', 'wire2', 'gate1', 'wire3', 'blk0', True, 3, 3, 1),
            ], nmos = [
               Transistor('NMOS_A', 'wire3', 'gate0', 'wire0', 'blk0', False, 3, 3, 1),
               Transistor('NMOS_B', 'wire5', 'gate1', 'wire6', 'blk0', False, 3, 3, 1)
            ], diffbreak = 1)

def tryplace(file):
  file = absolute(file)
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


def trytests(testname):
   tests = {
      'test1': test1,
      'test2': test2
   }
   return tests[testname]()

if __name__ == "__main__":
  argp = argparse.ArgumentParser()
  argp.add_argument('--place', type=str, required=False)
  argp.add_argument('--test', type=str, required=False)
  argp.add_argument('--split', type=str, required=False)
  args = argp.parse_args()
  if args.place != None:
    tryplace(args.place)
  elif args.test != None:
    trytests(args.test)
  elif args.split != None:
    print('splitting TODO --- file from ', args.split)
  else:
    print('usage: [--place|--test|--split] <name to test or CDL file>') 

