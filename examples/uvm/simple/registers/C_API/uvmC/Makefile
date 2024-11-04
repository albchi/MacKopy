#-------------------------------------------------------------
#    Copyright 2011 Synopsys, Inc.
#    All Rights Reserved Worldwide
#
# SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary work of
# Synopsys, Inc., and is fully protected under copyright and trade
# secret laws. You may not view, use, disclose, copy, or distribute this
# file or any information contained herein except pursuant to a valid
# written license from Synopsys.
#
#-------------------------------------------------------------


INCDIR	= ..

CFLAGS= -m64

plat:= $(shell vcs -platform )
ifeq  ($(plat),linux)
      CFLAGS:=-m32
endif


ifeq ($(plat),suse32)
      CFLAGS:=-m32
endif
      
ifeq ($(plat),sparcOS5)
      CFLAGS:=-m32 
endif



GCC	= gcc -c -pipe ${CFLAGS} -I. -I$(INCDIR) \
		-I$(VCS_HOME)/include \
		-I$(VCS_HOME)/etc/uvm-1.2/include/uvmC \
		-I$(VCS_HOME)/etc/uvm-1.2/include \
		-DSNPS_REG_NOP -DSNPS_REG_DEBUG -DSNPS_UVMC_ONLY

LD	= gcc -lstdc++

.cpp.o:
	$(GCC) $*.cpp



all: clean simv

ral_sys.sv: $(INCDIR)/regmodel/sys.ralf
	ralgen -t sys -uvm $(INCDIR)/regmodel/sys.ralf

ral_sys.h: $(INCDIR)/regmodel/sys.ralf
	ralgen -t sys -uvm -gen_c $(INCDIR)/regmodel/sys.ralf

simv: ral_sys.sv main.o sys_driver.o
	vcs -q -ntb_opts uvm-1.2 -sverilog  +define+SNPS_UVMC_ONLY \
		 test.sv main.o sys_driver.o 
	simv +UVM_VERBOSITY=UVM_MEDIUM

main.o: \
	ral_sys.h \
	$(INCDIR)/firmware/sys_driver.h

sys_driver.o: \
	$(INCDIR)/firmware/sys_driver.h \
	$(INCDIR)/firmware/sys_driver.cpp
	$(GCC) $(INCDIR)/firmware/sys_driver.cpp

clean:
	rm -rf *~ *.o simv* csrc vc_hdrs.h ucli.key ral_*

