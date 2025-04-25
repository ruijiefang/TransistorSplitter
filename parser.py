"""
  Parser and pairing code for netlist given in Circuit Design Language (CDL) format
"""
import re
import os
import z3

from sys import argv 
from collections import defaultdict
from overrides import overrides

#import sat_placer

class Transistor(object):
  """
    Representation of a transistor
    Example:
      MM13    net067    net063 VSS      VSS     nmos_slvt w=162.00n l=20n   nfin=6
      ^       ^         ^      ^        ^       ^         ^         ^       ^
      name    drain     gate   source   bulk    NMOS      width     length  numfins

    drain: output of the transistor
    gate: control-signal connection
    source: usually VDD, connected to a supply voltage for pMOS
    bulk: also tied to VDD
  """

  def __init__(self, name, drain, gate, src, blk, is_pmos, width, length, numfins):
    self.is_pmos = is_pmos
    self.width = width
    self.length = length
    self.numfins = numfins
    self.name = name
    self.drain = drain
    self.gate = gate
    self.src = src
    self.blk = blk

  def transistor_type(self):
    return "pmos_slvt" if self.is_pmos else "nmos_slvt"

  def __str__(self):
    return self.name + " " + \
      self.drain + " " + \
      self.gate + " " + \
      self.src + " " +  \
      self.blk + " " + \
      self.transistor_type() + " " + \
      "w=" + str(self.width) + "n " + \
      "l=" + str(self.length) + "n " + \
      "nfin=" + str(self.numfins)

class TransistorBlock(object):

  """
    a TransistorBlock is a collection of transistors with power source, input/output signals
      input_signal: commonly referred to as `A`
      output_signal: commonly referred to as `Y`
      vdd_name: name of VDD / power supply
      vss_name: name of VSS / ground
  """

  def __init__(self, name, externals, transistors=None):
    print('--------- transistors: ', transistors)
    self.transistors = transistors
    self.name = name
    self.externals = externals

  def add_transistor(self, tr):
    if self.transistors == None:
      self.transistors=[]
    self.transistors.append(tr)

  def add_externals(self, ex):
    self.externals.append(ex)

  def __str__(self):
    lines = []
    externals = " ".join(self.externals)
    lines.append(".SUBCKT " + self.name + " " + externals)
    for tr in self.transistors:
      lines.append(str(tr))
    lines.append(".ENDS")
    return "\n".join(lines)

class PairingPlan(object):
  """
    PairingPlan represents a possible pairing of a (pmos, nmos) list
  """
  def __init__(self, pmos, nmos, pairs={}):
    self.pmos = pmos
    self.nmos = nmos
    self.pairs = pairs
    if len(self.pmos) != len(self.nmos):
      raise ValueError("PairingPlan(): length of PMOS (" + str(len(pmos)) + ") != length of NMOS (" + str(len(nmos)) + ")")

  def pair(self, p, n):
    if self.p.gate != self.n.gate:
      raise ValueError("PairingPlan(): illegal pairing of " + p.name + " with " + n.name)
    self.pairs[p.name] = n.name
    self.pairs[n.name] = p.name

  def can_pair(self, p, n):
    return self.p.gate == self.n.gate

  # check if self.pairs[-] is idempotent
  def is_legal(self):
    for p in self.pairs:
      q = self.pairs[p]
      if self.pairs[q] != p:
        return False
      if self.pairs[q].is_pmos == self.pairs[p].is_pmos:
        return False
    return True

  # check if a pairing covers all pairs
  def is_complete(self):
    return (self.is_legal() and (len(self.pairs) == 2 * len(self.pmos)))

class PairedTransistorBlock(TransistorBlock):

  """
    a PairedTransistorBlock extends a TransistorBlock,
    it represents the paired result of a transistor block
  """
  def __init__(self, transblock, pairingplan):
    super().__init__(transblock.name, transblock.externals, transistors=transblock.transistors)
    self.pairingplan = pairingplan

  def pmos_nmos_pairs(self):
    pmos = list(filter(lambda tr: tr.is_pmos, self.transistors))
    pairs = []
    for p_tr in pmos:
      n_tr = self.pairingplan.pairs[p_tr]
      pairs.append((p_tr, n_tr))
    return pairs


class TransistorPairer(object):
  """
    Greedy placer for transistors
  """
  def __init__(self, transblock):
    self.transblock = transblock
    self.pmos_trs = list(filter(lambda x: x.is_pmos, self.transblock.transistors))
    self.nmos_trs = list(filter(lambda x: not(x.is_pmos), self.transblock.transistors))
    self.pmos_gate = defaultdict(list)
    self.nmos_gate = defaultdict(list)
    for tr in self.pmos_trs:
      self.pmos_gate[tr.gate].append(tr)
    for tr in self.nmos_trs:
      self.nmos_gate[tr.gate].append(tr)
    # Check #1: total num of PMOS transistors = total num of NMOS transistors
    if len(self.pmos_trs) != len(self.nmos_trs):
      raise ValueError("place(): unequal number of PMOS and NMOS transistors: num PMOS=" + str(len(self.pmos_trs)) + "; num NMOS=" + str(len(self.nmos_trs)))
    # Check #2: total num of PMOS gates = total num of NMOS gates
    if len(self.pmos_gate) != len(self.nmos_gate):
      raise ValueError("place(): unequal number of PMOS and NMOS gate names: num PMOS gates = " + str(len(self.pmos_gate)) + "; num NMOS gates = " + str(len(self.nmos_gate)))
    # Check #3: Number of pMOS = number of nMOS for each gate name
    for gate_name in self.pmos_gate:
      if len(self.pmos_gate[gate_name]) != len(self.nmos_gate[gate_name]):
        raise ValueError("place(): unequal number of PMOS and NMOS transistors for gate name " + gate_name + ": num PMOS=" + str(len(self.pmos_gate[gate_name])) + "; num NMOS=" + str(len(self.nmos_gate[gate_name])))


  def pairing(self):
    pairs = {}
    pmos_gate = self.pmos_gate
    nmos_gate = self.nmos_gate
    for gate_name in pmos_gate:
      # pair up in 1-1 fashion
      for i in range(len(pmos_gate[gate_name])):
        pairs[pmos_gate[gate_name][i]] = nmos_gate[gate_name][i]
        pairs[nmos_gate[gate_name][i]] = pmos_gate[gate_name][i]
    pairing = PairingPlan(self.pmos_trs, self.nmos_trs, pairs=pairs)
    result = PairedTransistorBlock(self.transblock, pairing) # list of (pmos, nmos) pairs
    assert pairing.pairs==pairs
    print('len(pairs): ', len(pairs))
    print('len(pmos_trs): ', len(self.pmos_trs))
    print('len(nmos_trs):', len(self.nmos_trs))
    print('len(result.pairingplan.pairs): ', len(result.pairingplan.pairs))
    assert len(result.pairingplan.pairs) == len(self.pmos_trs) * 2
    assert result.pairingplan.is_complete()
    return result


# TODO
class RuleChecker(object):
  def __init__(self, transblock):
    self.transblock = transblock


"""
  The following functions parse an input netlist given in CDL format
"""

def msplit(delimiters, string):
    regex_pattern = '|'.join(map(re.escape, delimiters))
    return re.split(regex_pattern, string)

def parse_term(vals, idx, s):
  try:
    t = float(vals[idx].split(s)[1].split("n")[0])
  except:
    t = float(vals[idx].split(s)[1].split("u")[0])
  return t

def parse_transistor(i, lines):
  line = lines[i].lstrip().rstrip()
  vals = msplit([' ', '\t'], line)
  print(" * >>>> ", vals)
  # ['MM2', 'net011', 'net012', 'VSS', 'VSS', 'nmos_slvt', 'w=810.0n', 'l=20n', 'nfin=30']
  # MM13 net067 net063 VSS VSS nmos_slvt w=162.00n l=20n nfin=6
  # 0    1      2       3   4   5         6        7     8
  tr_name = vals[0]
  tr_drain = vals[1]
  tr_gate = vals[2]
  tr_src = vals[3]
  tr_blk = vals[4]
  if ("pmos" in vals[5]) or ("nmos" in vals[5]):
    tr_is_pmos = ("pmos" in vals[5])
  else:
    raise ValueError("parse_transistor error: illegal input " + lines[i])
  tr_width = parse_term(vals, 6, "w=") # float(vals[6].split("w=")[1].split("n")[0])
  tr_length = parse_term(vals, 7, "l=") # float(vals[7].split("l=")[1].split("n")[0])
  tr_nfin = int(vals[8].split("nfin=")[1])
  return Transistor(tr_name, tr_drain, tr_gate, tr_src, tr_blk, tr_is_pmos, tr_width, tr_length, tr_nfin)

def parse_transblock(i, lines):
  if not(lines[i].startswith(".SUBCKT")):
    raise ValueError("parse_transblock error: input starts with: " + lines[i])
  line = lines[i].rstrip().lstrip()
  vals = msplit([' ', '\t'], line)
  print(" * >>> ", vals)
  # ['.SUBCKT', 'DECAPx10_ASAP7_75t_SL', 'VDD', 'VSS']
  #               ^1                      ^2     ^3
  externals = vals[2:]
  print('before')
  transblock = TransistorBlock(vals[1], externals)
  print("transblock: ", transblock.transistors)
  i += 1
  while True:
    line = lines[i].rstrip().lstrip()
    if line == "":
      i += 1
      continue
    if line.startswith("*"):
      i +=1
      continue
    if line.startswith('.ENDS'):
      print("finish parsing block ", transblock.name, "; ", len(transblock.transistors), ' transistors')
      return (transblock, i)
    else:
      tr = parse_transistor(i, lines)
      transblock.add_transistor(tr)
    i += 1

def parse_cdl(filename):
  with open(filename) as fd:
    lines = fd.readlines()

  transblocks = []
  i = 0
  while i < len(lines):
    l = lines[i].rstrip().lstrip()
    print('line: ', l)
    if l == "":
      i = i + 1
      continue
    if l.startswith(".SUBCKT"):
      transblock, _i = parse_transblock(i, lines)
      transblocks.append(transblock)
      i = _i + 1
    else:
      i = i + 1
      continue
  return transblocks

def print_cdl(transblocks):
  print(" ******** Parsed CDL file ******** ", len(transblocks), " blocks total")
  for transblock in transblocks:
    print("*** new block")
    print(str(transblock))
  print(" ***** end of input file *** ")

def absolute(path):
  return os.path.abspath(path)

def tryparser():
  if len(argv) != 2:
    raise ValueError("tryparser(): malformed argv string: " + "\t".join(argv))
  file = absolute(argv[1])
  print(" * CDL parser: parsing input file ", file)
  blocks = parse_cdl(file)
  print(" * CDL parser: parsing done. ")
  print_cdl(blocks)
  print("******************** trying pairing for each transistor block ***************")
  for block in blocks:
    print("*** pairing block ", block.name)
    pairer = TransistorPairer(block)
    result = pairer.pairing()
    print('* >>> pairing success')
    pairs = result.pmos_nmos_pairs()
    for (pmos, nmos) in pairs:
      print("* PAIR: ", pmos.name, " ; ", nmos.name)
  print("********")
  print('trying to generate a valid placement on grid')
  for block in blocks:
    pmos = list(filter(lambda x: x.is_pmos, block.transistors))
    nmos = list(filter(lambda x: not(x.is_pmos), block.transistors))
    placer = sat_placer.SATPlacement(1, 30, pmos, nmos, diffusion_break=1)
    print('placement result: ', placer.solve())
    placer.print_model()
    r = placer.parse_smt_result()
    c = sat_placer.Checker(r)
    c.check_source_drain_match()
    c.check_diffusion_break()
    c.check_jog()
    c.check_widths_sum_up_to_original_width()



if __name__ == "__main__":
  tryparser()