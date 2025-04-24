import parser
from parser import Transistor
from sat_placer import SATPlacement, Checker
from visualizer import Plotter

#parsed_file = parser.parse_cdl("examples/test.cdl")
#parser.print_cdl(parsed_file)
num_rows = 2
num_sites = 2
diffusion_break = 1
jog = 2
max_width = 3

print("\n\n**********************************\nStarting SAT Solver\n**********************************")
s = SATPlacement(
  num_rows = num_rows,
  num_sites = num_sites,
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
  , diffusion_break = diffusion_break # diffusion break
  )

s.solve()
results = s.parse_smt_result()
print("\nEnd solver\n\n")

for r in range(s.num_rows):
    for ss in range(s.num_sites):
        print('*** ResultBlock: ', results.pmos_cell_at(r, ss))
        print("*** ResultBlock", results.nmos_cell_at(r, ss))

print("**********************************\nStarting Checker\n**********************************")
checker = Checker(results, jog, diffusion_break, max_width)
check_sdm = checker.check_source_drain_match()
check_db = checker.check_diffusion_break()
check_width = checker.check_widths_sum_up_to_original_width()
check_jog = checker.check_jog()

if check_sdm and check_db and check_width and check_jog:
    print("\n***** Checker PASS")
else :
    print("\n***** Checker FAIL")
print("\nEnd checker\n\n")

plot = Plotter(results, num_sites, num_rows)
plot.plot()
plot.saveImage("test.png")


