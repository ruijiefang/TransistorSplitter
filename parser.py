"""
  Parser code for Circuit Design Language (CDL) format
"""
import re
import os
from sys import argv 

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

  def __init__(self, name, externals, transistors=[]):
    self.transistors = transistors
    self.name = name 
    self.externals = externals 

  def add_transistor(self, tr):
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
  def __init__(self, pmos, nmos):
    self.pmos = pmos 
    self.nmos = nmos
    self.pairs = {}
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
      n_tr = self.pairingplan.pairs[p_tr.name]
      pairs.append((p_tr, n_tr))
    return pairs


# TODO
class TransistorPairer(object):
  pass

# TODO 
class RuleChecker(object):
  def __init__(self, transblock):
    self.transblock = transblock 



def msplit(delimiters, string):
    regex_pattern = '|'.join(map(re.escape, delimiters))
    return re.split(regex_pattern, string)

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
  if vals[5] in ["nmos_slvt", "pmos_slvt"]:
    tr_is_pmos = vals[5] == "pmos_slvt"
  else:
    raise ValueError("parse_transistor error: illegal input " + lines[i])
  tr_width = float(vals[6].split("w=")[1].split("n")[0])
  tr_length = float(vals[7].split("l=")[1].split("n")[0])
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
  transblock = TransistorBlock(vals[1], externals)
    
  i += 1
  while True:
    line = lines[i].rstrip().lstrip()
    if line.startswith('.ENDS'):
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

if __name__ == "__main__":
  tryparser()
