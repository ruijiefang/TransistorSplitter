from pysat.formula import CNF
from pysat.solvers import Solver 

class Solver(object):
    def __init__(self):
        self.vars_to_int = {}
        self.int_to_vars = {}
        self.cnt = 0

    def add_var(self, v):
        self.vars_to_int[v] = self.cnt
        self.cnt += 1
        return self.vars_to_int[v]
    