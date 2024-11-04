VCS_AMS_HOME := ../../src
ifdef UVM_HOME
INCDIR = $(VCS_AMS_HOME)/uvm_ams.sv +incdir+$(VCS_AMS_HOME) +incdir+$(UVM_HOME)
else
INCDIR =$(VCS_AMS_HOME)/uvm_ams.sv -ntb_opts uvm-1.2 +incdir+$(VCS_AMS_HOME)
endif

all:	clean slew_checker_test stability_checker_test 

slew_checker_test :
	vcs -sverilog checker-sv_sync_slew.sv  -debug_acc+all -debug_region+cell+encrypt  -wreal res_min +define+UVM_SV_REAL_COMPAT_MODE +define+UVM_OBJECT_DO_NOT_NEED_CONSTRUCTOR $(INCDIR) 
	./simv +UVM_TESTNAME=slew_checker_test +define=UVM_SV_REAL_COMPAT_MODE 

stability_checker_test :
	vcs -sverilog checker-sv_sync_stability.sv  -debug_acc+all -debug_region+cell+encrypt  -wreal res_min $(INCDIR) +define+UVM_SV_REAL_COMPAT_MODE +define+UVM_OBJECT_DO_NOT_NEED_CONSTRUCTOR 
	./simv +UVM_TESTNAME=stability_checker_test +define=UVM_SV_REAL_COMPAT_MODE 

clean:
	rm -rf simv* csrc *.log vcdplus.vpd vc_hdrs.h ucli.key rad.v
