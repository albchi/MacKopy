echo "set_print_format for=vpd  file=merge" > ns.cfg;
echo "print_node_v *" >> ns.cfg;
cat spice/a2d.b4                > a2d.b4;
echo ".global vdd gnd"          >> a2d.b4;
echo "vsu vdd gnd 1.8"  >> a2d.b4;
echo ".end"                     >> a2d.b4;
echo "use_spice -cell A2DConverter;"            > vcsAD.init
echo "use_verilog -cell anaComparatorChecker;"  >> vcsAD.init;
echo "choose nanosim -n a2d.b4 -c ns.cfg;"      >> vcsAD.init
vcs -wreal res_def -debug_access+all  +ad verif/ana_tb.sv  \
-sverilog -realport -lca -ntb_opts uvm +incdir+ \
+incdir+./verif+./tests  -ams -timescale=1ns/1ps +define+SVA_AMS 

