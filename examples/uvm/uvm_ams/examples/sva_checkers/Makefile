VCS_AMS_HOME := ../../src
ifdef UVM_HOME
INCDIR = +incdir+$(VCS_AMS_HOME) +incdir+$(UVM_HOME)
else
INCDIR = -ntb_opts uvm-1.2 +incdir+$(VCS_AMS_HOME)
endif

all:	clean 02_checker-sva_async_threshold \

clean:
	rm -rf simv* csrc *.log vcdplus.vpd vc_hdrs.h ucli.key rad.v

0%:
	vcs -sverilog 0$*.sv -debug_access+pp  -wreal res_min $(INCDIR) | grep 'simv up to date'
	if [ -f ./simv ]; then ./simv | grep 'finish at simulation time';fi;
