## 
## -------------------------------------------------------------
##    Copyright 2010-2011 Synopsys, Inc.
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

DIR := ../sv
all: clean comp run

comp:
	if [ -d $(DIR) ]; then \
	(vcs -sverilog -timescale=1ns/1ns -debug_access+all +vpi -ntb_opts uvm-1.2 +incdir+$(DIR) ubus_tb_top.sv -l comp.log); \
	else \
	echo "copy the sv directory from ../sv"; \
	fi
run:
	simv  +UVM_NO_RELNOTES  -l simv.log +UVM_TESTNAME=test_2m_4s 

clean: 
	rm -rf csrc simv* vc_hdrs.h ucli.key urg* *.log
