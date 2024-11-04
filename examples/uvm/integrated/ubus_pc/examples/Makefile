# Makefile for PARTITION COMPILE basic example 


all: clean comp run comp_modify run_modify

clean:
	rm -rf simv* csrc* *.vpd *.key *.log work lib vc_hdrs.h partitionlib

comp : an compile_partcomp 

comp_modify: new_test compile_partcomp_modify



an:
	vlogan -sverilog -ntb_opts uvm-1.2 
	vlogan -sverilog -ntb_opts uvm-1.2  +incdir+../sv+./ ./ubus_tb_top.sv test.sv
	vlogan -sverilog ubus_topcfg.v

compile_partcomp:
	vcs -sverilog -ntb_opts uvm-1.2  -partcomp -partcomp_dir=./partitionlib -lca topcfg -debug_access+pp+f -timescale="1ns/1ps" -l comp.log

new_test:
	vlogan -sverilog test.sv  +incdir+../sv+./  -ntb_opts uvm-1.2 +define+new_test

compile_partcomp_modify:
	vcs -sverilog -ntb_opts uvm-1.2  -partcomp -partcomp_dir=./partitionlib -lca topcfg -debug_access+pp+f -timescale="1ns/1ps" -l compile_partcomp_modify.log

run:
	./simv  +UVM_NO_RELNOTES  -l simv1.log +UVM_TESTNAME=test_2m_4s 

run_modify:

	./simv  +UVM_NO_RELNOTES  -l simv2.log +UVM_TESTNAME=test_r8_w8_r4_w4
