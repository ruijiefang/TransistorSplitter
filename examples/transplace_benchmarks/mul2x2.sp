.SUBCKT mul2x2 a_1_ a_0_ b_1_ b_0_ y_3_ y_2_ y_1_ y_0_


* INVx1_ASAP7_6t_L U3
MMN0_U3_inst0_MM0 n1 a_1_ VSS VSS nmos_lvt w=54.0n l=20n 2
MMP1_U3_inst0_MM1 n1 a_1_ VDD VDD pmos_lvt w=54.0n l=20n 2

* INVx1_ASAP7_6t_L U4
MMN2_U4_inst1_MM0 n2 b_1_ VSS VSS nmos_lvt w=54.0n l=20n 2
MMP3_U4_inst1_MM1 n2 b_1_ VDD VDD pmos_lvt w=54.0n l=20n 2

* INVx1_ASAP7_6t_L U5
MMN4_U5_inst2_MM0 n3 b_0_ VSS VSS nmos_lvt w=54.0n l=20n 2
MMP5_U5_inst2_MM1 n3 b_0_ VDD VDD pmos_lvt w=54.0n l=20n 2

* NOR3x1f_ASAP7_6t_L U6
MMN6_U6_inst3_MM14 y_2_ n2 VSS VSS nmos_lvt w=54.0n l=20n 2
MMN7_U6_inst3_MM13 y_2_ n4 VSS VSS nmos_lvt w=54.0n l=20n 2
MMN8_U6_inst3_MM12 y_2_ n1 VSS VSS nmos_lvt w=54.0n l=20n 2
MMP9_U6_inst3_MM8 inst3_net21 n2 VDD VDD pmos_lvt w=54.0n l=20n 2
MMP10_U6_inst3_MM10 inst3_net22 n4 inst3_net21 VDD pmos_lvt w=54.0n l=20n 2
MMP11_U6_inst3_MM11 y_2_ n1 inst3_net22 VDD pmos_lvt w=54.0n l=20n 2

* NOR2xp5_ASAP7_6t_L U7
MMN12_U7_inst4_MM2 VSS n3 n4 VSS nmos_lvt w=27.0n l=20n 1
MMN13_U7_inst4_MM1 VSS n5 n4 VSS nmos_lvt w=27.0n l=20n 1
MMP14_U7_inst4_MM4 inst4_net16 n5 n4 VDD pmos_lvt w=54.0n l=20n 2
MMP15_U7_inst4_MM3 VDD n3 inst4_net16 VDD pmos_lvt w=54.0n l=20n 2

* XOR2xp5r_ASAP7_6t_L U8
MMP16_U8_inst5_MM4 VDD n6 inst5_net019 VDD pmos_lvt w=54.0n l=20n 2
MMP17_U8_inst5_MM5 VDD n5 inst5_net019 VDD pmos_lvt w=54.0n l=20n 2
MMP18_U8_inst5_MM6 inst5_net019 inst5_net036 y_1_ VDD pmos_lvt w=54.0n l=20n 2
MMP19_U8_inst5_MM2 inst5_net048 n5 inst5_net036 VDD pmos_lvt w=54.0n l=20n 2
MMP20_U8_inst5_MM3 VDD n6 inst5_net048 VDD pmos_lvt w=54.0n l=20n 2
MMN21_U8_inst5_MM11 VSS n6 inst5_net047 VSS nmos_lvt w=54.0n l=20n 2
MMN22_U8_inst5_MM10 inst5_net047 n5 y_1_ VSS nmos_lvt w=54.0n l=20n 2
MMN23_U8_inst5_MM9 VSS inst5_net036 y_1_ VSS nmos_lvt w=54.0n l=20n 2
MMN24_U8_inst5_MM0 VSS n6 inst5_net036 VSS nmos_lvt w=54.0n l=20n 2
MMN25_U8_inst5_MM1 VSS n5 inst5_net036 VSS nmos_lvt w=54.0n l=20n 2

* NAND2xp5R_ASAP7_6t_L U9
MMN26_U9_inst6_MM3 inst6_net16 b_1_ VSS VSS nmos_lvt w=54.0n l=20n 2
MMN27_U9_inst6_MM2 n5 a_0_ inst6_net16 VSS nmos_lvt w=54.0n l=20n 2
MMP28_U9_inst6_MM1 n5 a_0_ VDD VDD pmos_lvt w=54.0n l=20n 2
MMP29_U9_inst6_MM0 n5 b_1_ VDD VDD pmos_lvt w=54.0n l=20n 2

* NAND2xp5R_ASAP7_6t_L U10
MMN30_U10_inst7_MM3 inst7_net16 a_1_ VSS VSS nmos_lvt w=54.0n l=20n 2
MMN31_U10_inst7_MM2 n6 b_0_ inst7_net16 VSS nmos_lvt w=54.0n l=20n 2
MMP32_U10_inst7_MM1 n6 b_0_ VDD VDD pmos_lvt w=54.0n l=20n 2
MMP33_U10_inst7_MM0 n6 a_1_ VDD VDD pmos_lvt w=54.0n l=20n 2

* AND2x2_ASAP7_6t_L U11
MMP34_U11_inst8_MM4_0 y_3_ inst8_net10 VDD VDD pmos_lvt w=54.0n l=20n 2
MMP35_U11_inst8_MM4_1 y_3_ inst8_net10 VDD VDD pmos_lvt w=54.00n l=20n 2
MMP36_U11_inst8_MM1 inst8_net10 a_1_ VDD VDD pmos_lvt w=27.0n l=20n 1
MMP37_U11_inst8_MM0 inst8_net10 n4 VDD VDD pmos_lvt w=27.0n l=20n 1
MMN38_U11_inst8_MM5_0 y_3_ inst8_net10 VSS VSS nmos_lvt w=54.0n l=20n 2
MMN39_U11_inst8_MM5_1 y_3_ inst8_net10 VSS VSS nmos_lvt w=54.0n l=20n 2
MMN40_U11_inst8_MM3 inst8_net20 n4 VSS VSS nmos_lvt w=54.0n l=20n 2
MMN41_U11_inst8_MM2 inst8_net10 a_1_ inst8_net20 VSS nmos_lvt w=54.0n l=20n 2

* AND2x2_ASAP7_6t_L U12
MMP42_U12_inst9_MM4_0 y_0_ inst9_net10 VDD VDD pmos_lvt w=54.0n l=20n 2
MMP43_U12_inst9_MM4_1 y_0_ inst9_net10 VDD VDD pmos_lvt w=54.00n l=20n 2
MMP44_U12_inst9_MM1 inst9_net10 b_0_ VDD VDD pmos_lvt w=27.0n l=20n 1
MMP45_U12_inst9_MM0 inst9_net10 a_0_ VDD VDD pmos_lvt w=27.0n l=20n 1
MMN46_U12_inst9_MM5_0 y_0_ inst9_net10 VSS VSS nmos_lvt w=54.0n l=20n 2
MMN47_U12_inst9_MM5_1 y_0_ inst9_net10 VSS VSS nmos_lvt w=54.0n l=20n 2
MMN48_U12_inst9_MM3 inst9_net20 a_0_ VSS VSS nmos_lvt w=54.0n l=20n 2
MMN49_U12_inst9_MM2 inst9_net10 b_0_ inst9_net20 VSS nmos_lvt w=54.0n l=20n 2

.ENDS
