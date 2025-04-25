.SUBCKT adder4 a_3_ a_2_ a_1_ a_0_ b_3_ b_2_ b_1_ b_0_ y_3_ y_2_ y_1_ y_0_


* INVx1_ASAP7_6t_L U2
MMN0_U2_inst0_MM0 n1 a_2_ VSS VSS nmos_lvt w=54.0n l=20n nfin=2
MMP1_U2_inst0_MM1 n1 a_2_ VDD VDD pmos_lvt w=54.0n l=20n nfin=2

* INVx1_ASAP7_6t_L U3
MMN2_U3_inst1_MM0 n2 b_2_ VSS VSS nmos_lvt w=54.0n l=20n nfin=2
MMP3_U3_inst1_MM1 n2 b_2_ VDD VDD pmos_lvt w=54.0n l=20n nfin=2

* XOR2xp5r_ASAP7_6t_L U4
MMP4_U4_inst2_MM4 VDD n3 inst2_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP5_U4_inst2_MM5 VDD n4 inst2_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP6_U4_inst2_MM6 inst2_net019 inst2_net036 y_3_ VDD pmos_lvt w=54.0n l=20n nfin=2
MMP7_U4_inst2_MM2 inst2_net048 n4 inst2_net036 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP8_U4_inst2_MM3 VDD n3 inst2_net048 VDD pmos_lvt w=54.0n l=20n nfin=2
MMN9_U4_inst2_MM11 VSS n3 inst2_net047 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN10_U4_inst2_MM10 inst2_net047 n4 y_3_ VSS nmos_lvt w=54.0n l=20n nfin=2
MMN11_U4_inst2_MM9 VSS inst2_net036 y_3_ VSS nmos_lvt w=54.0n l=20n nfin=2
MMN12_U4_inst2_MM0 VSS n3 inst2_net036 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN13_U4_inst2_MM1 VSS n4 inst2_net036 VSS nmos_lvt w=54.0n l=20n nfin=2

* A2O1A1Ixp33_ASAP7_6t_L U5
MMN14_U5_inst3_MM7 inst3_net06 n2 VSS VSS nmos_lvt w=54.0n l=20n nfin=2
MMN15_U5_inst3_MM2 n4 n6 inst3_net06 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN16_U5_inst3_MM1 inst3_net015 n1 VSS VSS nmos_lvt w=54.0n l=20n nfin=2
MMN17_U5_inst3_MM0 inst3_net06 n5 inst3_net015 VSS nmos_lvt w=54.0n l=20n nfin=2
MMP18_U5_inst3_MM6 n4 n6 VDD VDD pmos_lvt w=54.0n l=20n nfin=2
MMP19_U5_inst3_MM5 n4 n2 inst3_net2 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP20_U5_inst3_MM4 inst3_net2 n1 VDD VDD pmos_lvt w=54.0n l=20n nfin=2
MMP21_U5_inst3_MM3 inst3_net2 n5 VDD VDD pmos_lvt w=54.0n l=20n nfin=2

* OR2x2_ASAP7_6t_L U6
MMN22_U6_inst4_MM5_1 VSS inst4_net7 n6 VSS nmos_lvt w=54.00n l=20n nfin=2
MMN23_U6_inst4_MM5_2 VSS inst4_net7 n6 VSS nmos_lvt w=54.00n l=20n nfin=2
MMN24_U6_inst4_MM1 VSS n5 inst4_net7 VSS nmos_lvt w=27.0n l=20n nfin=1
MMN25_U6_inst4_MM2 VSS n1 inst4_net7 VSS nmos_lvt w=27.0n l=20n nfin=1
MMP26_U6_inst4_MM0_1 VDD inst4_net7 n6 VDD pmos_lvt w=54.00n l=20n nfin=2
MMP27_U6_inst4_MM0_2 VDD inst4_net7 n6 VDD pmos_lvt w=54.00n l=20n nfin=2
MMP28_U6_inst4_MM4 inst4_net15 n5 inst4_net7 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP29_U6_inst4_MM3 VDD n1 inst4_net15 VDD pmos_lvt w=54.0n l=20n nfin=2

* XOR2xp5r_ASAP7_6t_L U7
MMP30_U7_inst5_MM4 VDD b_3_ inst5_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP31_U7_inst5_MM5 VDD a_3_ inst5_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP32_U7_inst5_MM6 inst5_net019 inst5_net036 n3 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP33_U7_inst5_MM2 inst5_net048 a_3_ inst5_net036 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP34_U7_inst5_MM3 VDD b_3_ inst5_net048 VDD pmos_lvt w=54.0n l=20n nfin=2
MMN35_U7_inst5_MM11 VSS b_3_ inst5_net047 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN36_U7_inst5_MM10 inst5_net047 a_3_ n3 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN37_U7_inst5_MM9 VSS inst5_net036 n3 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN38_U7_inst5_MM0 VSS b_3_ inst5_net036 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN39_U7_inst5_MM1 VSS a_3_ inst5_net036 VSS nmos_lvt w=54.0n l=20n nfin=2

* XOR2xp5r_ASAP7_6t_L U8
MMP40_U8_inst6_MM4 VDD n5 inst6_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP41_U8_inst6_MM5 VDD n7 inst6_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP42_U8_inst6_MM6 inst6_net019 inst6_net036 y_2_ VDD pmos_lvt w=54.0n l=20n nfin=2
MMP43_U8_inst6_MM2 inst6_net048 n7 inst6_net036 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP44_U8_inst6_MM3 VDD n5 inst6_net048 VDD pmos_lvt w=54.0n l=20n nfin=2
MMN45_U8_inst6_MM11 VSS n5 inst6_net047 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN46_U8_inst6_MM10 inst6_net047 n7 y_2_ VSS nmos_lvt w=54.0n l=20n nfin=2
MMN47_U8_inst6_MM9 VSS inst6_net036 y_2_ VSS nmos_lvt w=54.0n l=20n nfin=2
MMN48_U8_inst6_MM0 VSS n5 inst6_net036 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN49_U8_inst6_MM1 VSS n7 inst6_net036 VSS nmos_lvt w=54.0n l=20n nfin=2

* XOR2xp5r_ASAP7_6t_L U9
MMP50_U9_inst7_MM4 VDD n2 inst7_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP51_U9_inst7_MM5 VDD a_2_ inst7_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP52_U9_inst7_MM6 inst7_net019 inst7_net036 n7 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP53_U9_inst7_MM2 inst7_net048 a_2_ inst7_net036 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP54_U9_inst7_MM3 VDD n2 inst7_net048 VDD pmos_lvt w=54.0n l=20n nfin=2
MMN55_U9_inst7_MM11 VSS n2 inst7_net047 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN56_U9_inst7_MM10 inst7_net047 a_2_ n7 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN57_U9_inst7_MM9 VSS inst7_net036 n7 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN58_U9_inst7_MM0 VSS n2 inst7_net036 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN59_U9_inst7_MM1 VSS a_2_ inst7_net036 VSS nmos_lvt w=54.0n l=20n nfin=2

* MAJIxp5_ASAP7_6t_L U10
MMN60_U10_inst8_MM4 inst8_net17 n8 VSS VSS nmos_lvt w=54.0n l=20n nfin=2
MMN61_U10_inst8_MM3 n5 a_1_ inst8_net17 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN62_U10_inst8_MM2 inst8_net1 n8 VSS VSS nmos_lvt w=54.0n l=20n nfin=2
MMN63_U10_inst8_MM1 inst8_net1 a_1_ VSS VSS nmos_lvt w=54.0n l=20n nfin=2
MMN64_U10_inst8_MM0 n5 b_1_ inst8_net1 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN65_U10_inst8_MM10 n5 b_1_ inst8_net1 VSS nmos_lvt w=54.0n l=20n nfin=2
MMP66_U10_inst8_MM9 inst8_net16 n8 VDD VDD pmos_lvt w=54.0n l=20n nfin=2
MMP67_U10_inst8_MM8 n5 a_1_ inst8_net16 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP68_U10_inst8_MM7 inst8_net3 n8 VDD VDD pmos_lvt w=54.0n l=20n nfin=2
MMP69_U10_inst8_MM6 inst8_net3 a_1_ VDD VDD pmos_lvt w=54.0n l=20n nfin=2
MMP70_U10_inst8_MM5 n5 b_1_ inst8_net3 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP71_U10_inst8_MM11 n5 b_1_ inst8_net3 VDD pmos_lvt w=54.0n l=20n nfin=2

* XOR2xp5r_ASAP7_6t_L U11
MMP72_U11_inst9_MM4 VDD n8 inst9_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP73_U11_inst9_MM5 VDD n9 inst9_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP74_U11_inst9_MM6 inst9_net019 inst9_net036 y_1_ VDD pmos_lvt w=54.0n l=20n nfin=2
MMP75_U11_inst9_MM2 inst9_net048 n9 inst9_net036 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP76_U11_inst9_MM3 VDD n8 inst9_net048 VDD pmos_lvt w=54.0n l=20n nfin=2
MMN77_U11_inst9_MM11 VSS n8 inst9_net047 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN78_U11_inst9_MM10 inst9_net047 n9 y_1_ VSS nmos_lvt w=54.0n l=20n nfin=2
MMN79_U11_inst9_MM9 VSS inst9_net036 y_1_ VSS nmos_lvt w=54.0n l=20n nfin=2
MMN80_U11_inst9_MM0 VSS n8 inst9_net036 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN81_U11_inst9_MM1 VSS n9 inst9_net036 VSS nmos_lvt w=54.0n l=20n nfin=2

* XOR2xp5r_ASAP7_6t_L U12
MMP82_U12_inst10_MM4 VDD b_1_ inst10_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP83_U12_inst10_MM5 VDD a_1_ inst10_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP84_U12_inst10_MM6 inst10_net019 inst10_net036 n9 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP85_U12_inst10_MM2 inst10_net048 a_1_ inst10_net036 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP86_U12_inst10_MM3 VDD b_1_ inst10_net048 VDD pmos_lvt w=54.0n l=20n nfin=2
MMN87_U12_inst10_MM11 VSS b_1_ inst10_net047 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN88_U12_inst10_MM10 inst10_net047 a_1_ n9 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN89_U12_inst10_MM9 VSS inst10_net036 n9 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN90_U12_inst10_MM0 VSS b_1_ inst10_net036 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN91_U12_inst10_MM1 VSS a_1_ inst10_net036 VSS nmos_lvt w=54.0n l=20n nfin=2

* XOR2xp5r_ASAP7_6t_L U13
MMP92_U13_inst11_MM4 VDD b_0_ inst11_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP93_U13_inst11_MM5 VDD a_0_ inst11_net019 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP94_U13_inst11_MM6 inst11_net019 inst11_net036 y_0_ VDD pmos_lvt w=54.0n l=20n nfin=2
MMP95_U13_inst11_MM2 inst11_net048 a_0_ inst11_net036 VDD pmos_lvt w=54.0n l=20n nfin=2
MMP96_U13_inst11_MM3 VDD b_0_ inst11_net048 VDD pmos_lvt w=54.0n l=20n nfin=2
MMN97_U13_inst11_MM11 VSS b_0_ inst11_net047 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN98_U13_inst11_MM10 inst11_net047 a_0_ y_0_ VSS nmos_lvt w=54.0n l=20n nfin=2
MMN99_U13_inst11_MM9 VSS inst11_net036 y_0_ VSS nmos_lvt w=54.0n l=20n nfin=2
MMN100_U13_inst11_MM0 VSS b_0_ inst11_net036 VSS nmos_lvt w=54.0n l=20n nfin=2
MMN101_U13_inst11_MM1 VSS a_0_ inst11_net036 VSS nmos_lvt w=54.0n l=20n nfin=2

* AND2x2_ASAP7_6t_L U14
MMP102_U14_inst12_MM4_0 n8 inst12_net10 VDD VDD pmos_lvt w=54.0n l=20n nfin=2
MMP103_U14_inst12_MM4_1 n8 inst12_net10 VDD VDD pmos_lvt w=54.00n l=20n nfin=2
MMP104_U14_inst12_MM1 inst12_net10 a_0_ VDD VDD pmos_lvt w=27.0n l=20n nfin=1
MMP105_U14_inst12_MM0 inst12_net10 b_0_ VDD VDD pmos_lvt w=27.0n l=20n nfin=1
MMN106_U14_inst12_MM5_0 n8 inst12_net10 VSS VSS nmos_lvt w=54.0n l=20n nfin=2
MMN107_U14_inst12_MM5_1 n8 inst12_net10 VSS VSS nmos_lvt w=54.0n l=20n nfin=2
MMN108_U14_inst12_MM3 inst12_net20 b_0_ VSS VSS nmos_lvt w=54.0n l=20n nfin=2
MMN109_U14_inst12_MM2 inst12_net10 a_0_ inst12_net20 VSS nmos_lvt w=54.0n l=20n nfin=2

.ENDS
