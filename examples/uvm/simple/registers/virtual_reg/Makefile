all: clean ralgen comp run 
#Cleanup
clean:
	rm -rf  simv* csrc *.log *.hvp *.vpd vc_hdrs.h ucli.key urgReport VCS.log


ralgen:
	ralgen -l sv  -uvm  -t  host_regmodel  host.ralf 
	
comp:
	vcs -Xanish=0x32 -sverilog -ntb_opts uvm-1.2 -debug_access+all  -timescale="1ns/100ps" ./rtl/router_test_top.sv ./rtl/ral/router.sv ./rtl/router_io.sv ./rtl/ral/host_io.sv +incdir+./env +incdir+./tests +incdir+./sequence ./sequence/packet_seq_lib_pkg.sv ./tests/test.sv -l comp.log 


run: 
	simv +ntb_random_seed=1 +UVM_TESTNAME=test_ral_seq -l run.log 


