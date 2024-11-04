#!/bin/csh -f
setenv VCS_AMS_HOME ../../src


cat spice/a2d.b4                > a2d.b4;
echo ".global vdd gnd"          >> a2d.b4;
echo "vsu vdd gnd 1.8"  >> a2d.b4;
echo ".end"                     >> a2d.b4;
echo "use_spice -cell A2DConverter;"            > hsim.init;
echo "use_verilog -cell anaComparatorChecker;"  >> hsim.init;
echo "choose hsim a2d.b4;"                      >> hsim.init;
echo "set rmap spice/inv.map;"                  >> hsim.init;
echo "set bus_format _%d;"                      >> hsim.init;

vcs -wreal res_def -debug_access+all  -wreal res_def -debug_access+all  -ad=hsim.init verif/ana_tb.sv  -sverilog -realport -lca -ntb_opts uvm +incdir+. +incdir+./verif+./tests -timescale=1ns/1ps  +incdir+./../../src +incdir+$VCS_AMS_HOME
