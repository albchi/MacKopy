ifndef TEST
TESTNAME = +UVM_TESTNAME=test_multi_gen
else
TESTNAME = +UVM_TESTNAME=$(TEST)
endif

ifndef UVM_HOME
UVM = -ntb_opts uvm-1.2 
else
UVM = +incdir+$(UVM_HOME) $(UVM_HOME)/uvm_pkg.sv $(UVM_HOME)/dpi/uvm_dpi.cc 
endif

ifndef VDD
VDD = 1.8
endif

FILE_LIST = verif/ana_tb.sv 

ifdef SVA
VCS_OPT := $(VCS_OPT) +define+SVA_AMS 
endif

TESTLIST = test_rand \
	   test_ramp \
	   test_multi_gen

default: xa

all: xa

clean:
	\rm -rf simv* csrc
	\rm -rf vc_hdrs.h ucli.key *.log
	\rm -rf vcdplus.vpd novas.*
	\rm -rf work/*
	\rm -rf out/*
	\rm -rf hsim.fsdb hsim.conn NULL
	\rm -rf urgReport

xa_comp: 
	./comp_xa.csh

xa_run:
	./run_xa.csh

xa: clean xa_comp xa_run

regression:
	for Test in $(TESTLIST); do \
		./simv -l $$Test.log +UVM_TESTNAME=$$Test; \
	done;

urg:
	urg -full64 -format text -dir simv.vdb/
	cat urgReport/groups.txt

