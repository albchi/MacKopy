VCS_AMS_HOME := ../../src
ifdef UVM_HOME
INCDIR = $(VCS_AMS_HOME)/uvm_ams.sv +incdir+$(VCS_AMS_HOME) +incdir+$(UVM_HOME)
else
INCDIR =$(VCS_AMS_HOME)/uvm_ams.sv -ntb_opts uvm-1.2 +incdir+$(VCS_AMS_HOME)
endif


all: clean 04_custom_src_gen

clean:
	\rm -rf simv* csrc
	\rm -rf vc_hdrs.h ucli.key *.log
	\rm -rf vcdplus.vpd

0%:
	vcs -sverilog 0$*.sv $(INCDIR) -wreal res_def -debug_access+pp 
	./simv +UVM_TESTNAME=test +UVM_VERBOSITY=debug -l 0$*.log
