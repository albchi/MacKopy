#!/bin/csh -f 

## Addition of new test to test block ##

vlogan -sverilog test.sv  +incdir+../sv+./  -ntb_opts uvm +define+new_test  

## Recompilation step in partition compile flow   ## 

vcs -sverilog -ntb_opts uvm -partcomp topcfg -partcomp_dir=partitionlib  -debug_access+pp+f -timescale="1ns/1ps"

simv  +UVM_NO_RELNOTES  -l simv2.log  +UVM_TESTNAME=test_r8_w8_r4_w4
