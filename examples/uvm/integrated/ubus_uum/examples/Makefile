# Makefile for UUM basic example 


all: clean comp run

clean:
	rm -rf simv* csrc* *.vpd *.key *.log work  vc_hdrs.h 

comp : an compile


an:
	vlogan -sverilog -ntb_opts uvm-1.2 
	vhdlan bidir.vhd
	vlogan -sverilog -ntb_opts uvm-1.2 dut_dummy.v +incdir+../sv+./ ./ubus_tb_top.sv ./test.sv


compile:
	vcs -sverilog -ntb_opts uvm-1.2  ubus_tb_top -debug_access+all  -lca -l comp.log


run:
	./simv  +UVM_NO_RELNOTES +UVM_TESTNAME=test_2m_4s  -l simv.log
