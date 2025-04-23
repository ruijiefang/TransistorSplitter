import unittest
from sat_placer import Checker, ResultBlock, Result
from parser import Transistor

class JogTest(unittest.TestCase):
    def setUp(self):
        self.p1_1 = ResultBlock(1, "S-D", Transistor("p1_1", "", "", "", "", True, 100, 100, 1))
        self.p1_2 = ResultBlock(1, "S-D", Transistor("p1_2", "", "", "", "", True, 100, 100, 1))
        self.p1_3 = ResultBlock(1, "S-D", Transistor("p1_3", "", "", "", "", True, 100, 100, 1))
        self.p1_4 = ResultBlock(1, "S-D", Transistor("p1_4", "", "", "", "", True, 100, 100, 1))
        self.p1_5 = ResultBlock(1, "S-D", Transistor("p1_5", "", "", "", "", True, 100, 100, 1))

        self.p2_1 = ResultBlock(2, "S-D", Transistor("p2_1", "", "", "", "", True, 100, 100, 2))
        self.p2_2 = ResultBlock(2, "S-D", Transistor("p2_2", "", "", "", "", True, 100, 100, 2))
        self.p2_3 = ResultBlock(2, "S-D", Transistor("p2_3", "", "", "", "", True, 100, 100, 2))
        self.p2_4 = ResultBlock(2, "S-D", Transistor("p2_4", "", "", "", "", True, 100, 100, 2))
        self.p2_5 = ResultBlock(2, "S-D", Transistor("p2_5", "", "", "", "", True, 100, 100, 2))

        self.p3_1 = ResultBlock(3, "S-D", Transistor("p3_1", "", "", "", "", True, 100, 100, 3))
        self.p3_2 = ResultBlock(3, "S-D", Transistor("p3_2", "", "", "", "", True, 100, 100, 3))
        self.p3_3 = ResultBlock(3, "S-D", Transistor("p3_3", "", "", "", "", True, 100, 100, 3))
        self.p3_4 = ResultBlock(3, "S-D", Transistor("p3_4", "", "", "", "", True, 100, 100, 3))
        self.p3_5 = ResultBlock(3, "S-D", Transistor("p3_5", "", "", "", "", True, 100, 100, 3))

        self.n1_1 = ResultBlock(1, "S-D", Transistor("n1_1", "", "", "", "", False, 100, 100, 1))
        self.n1_2 = ResultBlock(1, "S-D", Transistor("n1_2", "", "", "", "", False, 100, 100, 1))
        self.n1_3 = ResultBlock(1, "S-D", Transistor("n1_3", "", "", "", "", False, 100, 100, 1))
        self.n1_4 = ResultBlock(1, "S-D", Transistor("n1_4", "", "", "", "", False, 100, 100, 1))
        self.n1_5 = ResultBlock(1, "S-D", Transistor("n1_5", "", "", "", "", False, 100, 100, 1))

        self.n2_1 = ResultBlock(2, "S-D", Transistor("n2_1", "", "", "", "", False, 100, 100, 2))
        self.n2_2 = ResultBlock(2, "S-D", Transistor("n2_2", "", "", "", "", False, 100, 100, 2))
        self.n2_3 = ResultBlock(2, "S-D", Transistor("n2_3", "", "", "", "", False, 100, 100, 2))
        self.n2_4 = ResultBlock(2, "S-D", Transistor("n2_4", "", "", "", "", False, 100, 100, 2))
        self.n2_5 = ResultBlock(2, "S-D", Transistor("n2_5", "", "", "", "", False, 100, 100, 2))

        self.n3_1 = ResultBlock(3, "S-D", Transistor("n3_1", "", "", "", "", False, 100, 100, 3))
        self.n3_2 = ResultBlock(3, "S-D", Transistor("n3_2", "", "", "", "", False, 100, 100, 3))
        self.n3_3 = ResultBlock(3, "S-D", Transistor("n3_3", "", "", "", "", False, 100, 100, 3))
        self.n3_4 = ResultBlock(3, "S-D", Transistor("n3_4", "", "", "", "", False, 100, 100, 3))
        self.n3_5 = ResultBlock(3, "S-D", Transistor("n3_5", "", "", "", "", False, 100, 100, 3))

    def test1(self):
        self.pmos_grid = [self.p3_1, self.p2_1, self.p2_2, self.p1_1]
        self.nmos_grid = [self.n1_1, self.n2_1, self.n2_2, self.n3_1]

        self.result = Result(1, 4, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nJog Test 1:")
        assert self.checker.check_jog() == True

    def test2(self):
        self.pmos_grid = [self.p3_1, self.p1_1, self.p2_1, self.p1_2]
        self.nmos_grid = [self.n1_1, self.n2_1, self.n2_2, self.n3_1]

        self.result = Result(1, 4, self.pmos_grid, self.nmos_grid)

        print("\nJog Test 2:")
        self.checker = Checker(self.result)

        assert self.checker.check_jog() == False

    def test3(self):
        self.pmos_grid = [self.p1_1, self.p3_1, self.p1_2, self.p2_1]
        self.nmos_grid = [self.n1_1, self.n2_1, self.n2_2, self.n3_1]

        self.result = Result(1, 4, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nJog Test 3:")
        assert self.checker.check_jog() == False

    def test4(self):
        self.pmos_grid = [self.p3_1, self.p2_1, self.p2_2, self.p1_1, self.p1_2, self.p3_2, self.p1_3, self.p2_3]
        self.nmos_grid = [self.n1_1, self.n2_1, self.n2_2, self.n3_1, self.n1_2, self.n2_3, self.n2_4, self.n3_2]

        self.result = Result(2, 4, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nJog Test 4:")
        assert self.checker.check_jog() == False

    def test5(self):
        self.pmos_grid = [self.p1_1, self.p2_1, self.p2_2, self.p3_1]
        self.nmos_grid = [self.n1_1, self.n3_1, self.n1_2, self.n2_1]

        self.result = Result(1, 4, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nJog Test 3:")
        assert self.checker.check_jog() == False


class WidthAddTest(unittest.TestCase):
    def setUp(self):
        self.p1 = Transistor("p1", "", "", "", "", True, 100, 100, 1)
        self.p2 = Transistor("p2", "", "", "", "", True, 100, 100, 2)
        self.p3 = Transistor("p3", "", "", "", "", True, 100, 100, 3)
        self.p4 = Transistor("p4", "", "", "", "", True, 100, 100, 4)
        self.p5 = Transistor("p5", "", "", "", "", True, 100, 100, 5)
        self.p6 = Transistor("p6", "", "", "", "", True, 100, 100, 6)

        self.n1 = Transistor("n1", "", "", "", "", False, 100, 100, 1)
        self.n2 = Transistor("n2", "", "", "", "", False, 100, 100, 2)
        self.n3 = Transistor("n3", "", "", "", "", False, 100, 100, 3)
        self.n4 = Transistor("n4", "", "", "", "", False, 100, 100, 4)
        self.n5 = Transistor("n5", "", "", "", "", False, 100, 100, 5)
        self.n6 = Transistor("n6", "", "", "", "", False, 100, 100, 6)

    def test1(self):
        self.bp1 = ResultBlock(1, "S-D", self.p1)
        self.bp2 = ResultBlock(2, "S-D", self.p2)
        self.bp3 = ResultBlock(3, "S-D", self.p3)
        self.bp4 = ResultBlock(2, "S-D", self.p4)
        self.bp5 = ResultBlock(2, "S-D", self.p4)
        self.bp6 = ResultBlock(3, "S-D", self.p5)
        self.bp7 = ResultBlock(2, "S-D", self.p5)
        self.bp8 = ResultBlock(3, "S-D", self.p6)
        self.bp9 = ResultBlock(3, "S-D", self.p6)
        self.bp10 = ResultBlock(0, "S-D", None)

        self.bn1 = ResultBlock(1, "S-D", self.n1)
        self.bn2 = ResultBlock(2, "S-D", self.n2)
        self.bn3 = ResultBlock(3, "S-D", self.n3)
        self.bn4 = ResultBlock(3, "S-D", self.n4)
        self.bn5 = ResultBlock(1, "S-D", self.n4)
        self.bn6 = ResultBlock(2, "S-D", self.n5)
        self.bn7 = ResultBlock(3, "S-D", self.n5)
        self.bn8 = ResultBlock(3, "S-D", self.n6)
        self.bn9 = ResultBlock(3, "S-D", self.n6)
        self.bn10 = ResultBlock(0, "S-D", None)

        self.pmos_grid = [self.bp1, self.bp2, self.bp3, self.bp4, self.bp5, self.bp6, self.bp7, self.bp8, self.bp9, self.bp10]
        self.nmos_grid = [self.bn1, self.bn2, self.bn3, self.bn4, self.bn5, self.bn6, self.bn7, self.bn8, self.bn9, self.bn10]

        self.result = Result(2, 5, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nWidth Sum Test 1:")
        assert self.checker.check_widths_sum_up_to_original_width() == True

    def test2(self):
        self.bp1 = ResultBlock(1, "S-D", self.p1)
        self.bp2 = ResultBlock(2, "S-D", self.p2)
        self.bp3 = ResultBlock(3, "S-D", self.p3)
        self.bp4 = ResultBlock(2, "S-D", self.p4)
        self.bp5 = ResultBlock(2, "S-D", self.p4)
        self.bp6 = ResultBlock(3, "S-D", self.p5)
        self.bp7 = ResultBlock(2, "S-D", self.p5)
        self.bp8 = ResultBlock(3, "S-D", self.p6)
        self.bp9 = ResultBlock(3, "S-D", self.p6)
        self.bp10 = ResultBlock(1, "S-D", self.p6)

        self.bn1 = ResultBlock(1, "S-D", self.n1)
        self.bn2 = ResultBlock(2, "S-D", self.n2)
        self.bn3 = ResultBlock(3, "S-D", self.n3)
        self.bn4 = ResultBlock(3, "S-D", self.n4)
        self.bn5 = ResultBlock(1, "S-D", self.n4)
        self.bn6 = ResultBlock(2, "S-D", self.n5)
        self.bn7 = ResultBlock(3, "S-D", self.n5)
        self.bn8 = ResultBlock(3, "S-D", self.n6)
        self.bn9 = ResultBlock(3, "S-D", self.n6)
        self.bn10 = ResultBlock(0, "S-D", None)

        self.pmos_grid = [self.bp1, self.bp2, self.bp3, self.bp4, self.bp5, self.bp6, self.bp7, self.bp8, self.bp9, self.bp10]
        self.nmos_grid = [self.bn1, self.bn2, self.bn3, self.bn4, self.bn5, self.bn6, self.bn7, self.bn8, self.bn9, self.bn10]

        self.result = Result(2, 5, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nWidth Sum Test 2:")
        assert self.checker.check_widths_sum_up_to_original_width() == False

    def test3(self):
        self.bp1 = ResultBlock(1, "S-D", self.p1)
        self.bp2 = ResultBlock(2, "S-D", self.p2)
        self.bp3 = ResultBlock(3, "S-D", self.p3)
        self.bp4 = ResultBlock(2, "S-D", self.p4)
        self.bp5 = ResultBlock(1, "S-D", self.p4)
        self.bp6 = ResultBlock(2, "S-D", self.p5)
        self.bp7 = ResultBlock(2, "S-D", self.p5)
        self.bp8 = ResultBlock(1, "S-D", self.p6)
        self.bp9 = ResultBlock(3, "S-D", self.p6)
        self.bp10 = ResultBlock(0, "S-D", None)

        self.bn1 = ResultBlock(1, "S-D", self.n1)
        self.bn2 = ResultBlock(2, "S-D", self.n2)
        self.bn3 = ResultBlock(2, "S-D", self.n3)
        self.bn4 = ResultBlock(3, "S-D", self.n4)
        self.bn5 = ResultBlock(1, "S-D", self.n4)
        self.bn6 = ResultBlock(1, "S-D", self.n5)
        self.bn7 = ResultBlock(3, "S-D", self.n5)
        self.bn8 = ResultBlock(2, "S-D", self.n6)
        self.bn9 = ResultBlock(3, "S-D", self.n6)
        self.bn10 = ResultBlock(0, "S-D", None)

        self.pmos_grid = [self.bp1, self.bp2, self.bp3, self.bp4, self.bp5, self.bp6, self.bp7, self.bp8, self.bp9, self.bp10]
        self.nmos_grid = [self.bn1, self.bn2, self.bn3, self.bn4, self.bn5, self.bn6, self.bn7, self.bn8, self.bn9, self.bn10]

        self.result = Result(2, 5, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nWidth Sum Test 3:")
        assert self.checker.check_widths_sum_up_to_original_width() == False

class DiffusionBreakTest(unittest.TestCase):
    def setUp(self):
        self.p1_1 = ResultBlock(1, "S-D", Transistor("p1_1", "", "", "", "", True, 100, 100, 1))
        self.p1_2 = ResultBlock(1, "S-D", Transistor("p1_2", "", "", "", "", True, 100, 100, 1))
        self.p1_3 = ResultBlock(1, "S-D", Transistor("p1_3", "", "", "", "", True, 100, 100, 1))
        self.p1_4 = ResultBlock(1, "S-D", Transistor("p1_4", "", "", "", "", True, 100, 100, 1))
        self.p1_5 = ResultBlock(1, "S-D", Transistor("p1_5", "", "", "", "", True, 100, 100, 1))
        self.p1_6 = ResultBlock(1, "S-D", Transistor("p1_6", "", "", "", "", True, 100, 100, 1))
        self.p1_7 = ResultBlock(1, "S-D", Transistor("p1_7", "", "", "", "", True, 100, 100, 1))
        self.p1_8 = ResultBlock(1, "S-D", Transistor("p1_8", "", "", "", "", True, 100, 100, 1))

        self.p0_1 = ResultBlock(0, "S-D", None)
        self.p0_2 = ResultBlock(0, "S-D", None)
        self.p0_3 = ResultBlock(0, "S-D", None)
        self.p0_4 = ResultBlock(0, "S-D", None)

        self.n1_1 = ResultBlock(1, "S-D", Transistor("n1_1", "", "", "", "", False, 100, 100, 1))
        self.n1_2 = ResultBlock(1, "S-D", Transistor("n1_2", "", "", "", "", False, 100, 100, 1))
        self.n1_3 = ResultBlock(1, "S-D", Transistor("n1_3", "", "", "", "", False, 100, 100, 1))
        self.n1_4 = ResultBlock(1, "S-D", Transistor("n1_4", "", "", "", "", False, 100, 100, 1))
        self.n1_5 = ResultBlock(1, "S-D", Transistor("n1_5", "", "", "", "", False, 100, 100, 1))
        self.n1_6 = ResultBlock(1, "S-D", Transistor("n1_6", "", "", "", "", False, 100, 100, 1))
        self.n1_7 = ResultBlock(1, "S-D", Transistor("n1_7", "", "", "", "", False, 100, 100, 1))
        self.n1_8 = ResultBlock(1, "S-D", Transistor("n1_8", "", "", "", "", False, 100, 100, 1))

        self.n0_1 = ResultBlock(0, "S-D", None)
        self.n0_2 = ResultBlock(0, "S-D", None)
        self.n0_3 = ResultBlock(0, "S-D", None)
        self.n0_4 = ResultBlock(0, "S-D", None)

    def test1(self):
        self.pmos_grid = [self.p1_1, self.p1_2, self.p1_3, self.p1_4]
        self.nmos_grid = [self.n1_1, self.n1_2, self.n1_3, self.n1_4]

        self.result = Result(1, 4, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nDiffusion Break Test 1:")
        assert self.checker.check_diffusion_break() == True

    def test2(self):
        self.pmos_grid = [self.p1_1, self.p0_1, self.p0_2, self.p1_4]
        self.nmos_grid = [self.n0_1, self.n0_2, self.n1_1, self.n1_2]

        self.result = Result(1, 4, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nDiffusion Break Test 2:")
        assert self.checker.check_diffusion_break() == True

    def test3(self):
        self.pmos_grid = [self.p1_1, self.p0_1, self.p1_4, self.p1_5]
        self.nmos_grid = [self.n1_1, self.n1_2, self.n0_1, self.n0_2]

        self.result = Result(1, 4, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nDiffusion Break Test 3:")
        assert self.checker.check_diffusion_break() == False

    def test4(self):
        self.pmos_grid = [self.p1_1, self.p1_2, self.p0_1, self.p1_3]
        self.nmos_grid = [self.n1_1, self.n1_2, self.n1_3, self.n0_1]

        self.result = Result(1, 4, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nDiffusion Break Test 4:")
        assert self.checker.check_diffusion_break() == False

    def test5(self):
        self.pmos_grid = [self.p0_1, self.p0_2, self.p0_3, self.p0_4]
        self.nmos_grid = [self.n0_1, self.n0_2, self.n0_3, self.n0_4]

        self.result = Result(1, 4, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nDiffusion Break Test 5:")
        assert self.checker.check_diffusion_break() == True

    def test6(self):
        self.pmos_grid = [self.p1_1, self.p1_2, self.p0_1, self.p1_3,
                          self.p1_4, self.p1_5, self.p0_2, self.p1_6]
        self.nmos_grid = [self.n1_1, self.n1_2, self.n1_3, self.n0_1,
                          self.n0_1, self.n1_4, self.n1_5, self.n1_6]

        self.result = Result(2, 4, self.pmos_grid, self.nmos_grid)

        self.checker = Checker(self.result)

        print("\nDiffusion Break Test 6:")
        assert self.checker.check_diffusion_break() == False

"""class NetMismatchTest(unittest.TestCase):
    def setUp(self):
        self.p1_1 = ResultBlock(1, Transistor("p1_1", "", "", "", "", True, 100, 100, 1))
        self.p1_2 = ResultBlock(1, Transistor("p1_2", "", "", "", "", True, 100, 100, 1))
        self.p1_3 = ResultBlock(1, Transistor("p1_3", "", "", "", "", True, 100, 100, 1))
        self.p1_4 = ResultBlock(1, Transistor("p1_4", "", "", "", "", True, 100, 100, 1))
        self.p1_5 = ResultBlock(1, Transistor("p1_5", "", "", "", "", True, 100, 100, 1))
        self.p1_6 = ResultBlock(1, Transistor("p1_6", "", "", "", "", True, 100, 100, 1))
        self.p1_7 = ResultBlock(1, Transistor("p1_7", "", "", "", "", True, 100, 100, 1))
        self.p1_8 = ResultBlock(1, Transistor("p1_8", "", "", "", "", True, 100, 100, 1))
"""
if __name__ == "__main__":
    unittest.main()