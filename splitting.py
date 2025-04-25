from parser import Transistor 
from parser import TransistorBlock

class SplitTransformer(object):

    def __init__(self, transblock):
        self.transblock = transblock
        self.pmos = list(filter(lambda x: x.is_pmos, transblock.transistors))
        self.nmos = list(filter(lambda x: not(x.is_pmos), transblock.transistors))

        self.splitted_pmos = []
        self.splitted_nmos = []

        self.pmos_to_splitted = {}
        self.nmos_to_splitted = {}

        for p in self.pmos:
            assert p.is_pmos
            self.pmos_to_splitted[p.name] = []
            if p.numfins > 1:
                for i in range(p.numfins):
                    sp_i = Transistor(p.name + '_splitted_p_' + str(i), p.drain, p.gate, p.src, p.blk, p.is_pmos, int(p.width / p.numfins), p.length, numfins = 1)
                    self.splitted_pmos.append(sp_i)
                    self.pmos_to_splitted[p.name].append(sp_i)
            else:
                self.pmos_to_splitted[p.name].append(p)
        for n in self.nmos:
            assert not(n.is_pmos)
            self.nmos_to_splitted[n.name] = []
            if n.numfins > 1:
                for i in range(n.numfins):
                    sn_i = Transistor(n.name + '_splitted_n_' + str(i), n.drain, n.gate, n.src, n.blk, n.is_pmos, int(n.width/n.numfins), n.length, numfins = 1)
                    self.splitted_nmos.append(sn_i)
                    self.nmos_to_splitted[n.name].append(sn_i)
            else:
                self.nmos_to_splitted[n.name].append(n)

        print('SplitTransformer: input has ', len(self.pmos), ' PMOSes')
        print('SplitTransformer: input has ', len(self.nmos), ' NMOSes')
        print('SplitTransformer: splitted input into ', len(self.splitted_pmos), ' PMOSes')
        print('SplitTransformer: splitted input into ', len(self.splitted_nmos), ' NMOSes')


        #self.sharing = {}
        #for x in self.pmos:
        #    self.sharing[x] = {}
        #    for y in self.pmos:
        #        if x.name != y.name:
        #            self.sharing[x][y] = False