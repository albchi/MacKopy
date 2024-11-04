## 
## -------------------------------------------------------------
##    Copyright 2004-2009 Synopsys, Inc.
##    All Rights Reserved Worldwide
## 
##    Licensed under the Apache License, Version 2.0 (the
##    "License"); you may not use this file except in
##    compliance with the License.  You may obtain a copy of
##    the License at
## 
##        http://www.apache.org/licenses/LICENSE-2.0
## 
##    Unless required by applicable law or agreed to in
##    writing, software distributed under the License is
##    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
##    CONDITIONS OF ANY KIND, either express or implied.  See
##    the License for the specific language governing
##    permissions and limitations under the License.
## -------------------------------------------------------------
##



all: clean comp run

DIR := ../../../integrated/apb
clean:
	rm -rf simv* csrc *.log vc_hdrs.h ucli.key

comp:
	if [ -d $(DIR) ]; then \
	(ralgen -uvm -t slave slave.ralf); \
	(vcs -sverilog -timescale=1ns/1ns -ntb_opts uvm-1.2 +incdir+$(DIR) tb_top.sv +define+RALGEN	test.sv -l comp.log); \
	else \
	echo "############################################################"; \
	echo "#  The primer Example has dependencies on other directories "; \
	echo "#  Please follow the steps mentioned below "; \
	echo "#  copy ${VCS_HOME}/doc/examples/uvm"; \
	echo "#  cd simple/registers/primer"; \
	echo "#  make to run"; \
	echo "############################################################"; \
	exit 0; \
	fi \

run:
	simv +UVM_NO_RELNOTES +UVM_TESTNAME=cmdline_test +UVM_REG_SEQ=uvm_reg_hw_reset_seq -l run.log

	simv +UVM_NO_RELNOTES +UVM_TESTNAME=cmdline_test +UVM_REG_SEQ=user_test_seq -l run_cmdline.log
