VCS_AMS_HOME := ../../src
ifdef UVM_HOME
INCDIR = $(VCS_AMS_HOME)/uvm_ams.sv +incdir+$(VCS_AMS_HOME) +incdir+$(UVM_HOME)
else
INCDIR =$(VCS_AMS_HOME)/uvm_ams.sv -ntb_opts uvm-1.2 +incdir+$(VCS_AMS_HOME)
endif


all: clean cmp

clean:
	\rm -rf simv* csrc sim.log
	\rm -rf vc_hdrs.h ucli.key

cmp:
	vcs -sverilog amp.sv amp_tb.sv $(INCDIR) -wreal res_def 
	./simv -l sim.log
