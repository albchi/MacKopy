UVM_TESTNAME = test_read_modify_write

DIR := ../sv 
all: clean comp run 

clean:
	rm -rf simv* csrc vcdplus.vpd urgReport tr.log ucli.key vc_hdrs.h DVEfiles

comp: clean 
	if [ -d $(DIR) ]; then \
	(vcs -lca -sverilog -timescale=1ns/1ns +define+UVM_TR_RECORD -debug_access+all  -ntb_opts uvm-1.2 +incdir+$(DIR) xbus_tb_top.sv  -l comp.log); \
	else \
	echo "copy the sv directory from ../sv"; \
	fi

run:
	simv  +UVM_NO_RELNOTES  +UVM_TESTNAME=$(UVM_TESTNAME) +UVM_LOG_RECORD +UVM_TR_RECORD  
