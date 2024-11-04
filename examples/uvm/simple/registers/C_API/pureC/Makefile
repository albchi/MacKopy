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

GCC	= gcc -c -I. -I$(INCDIR)/firmware -I$(INCDIR) \
		-I$(VCS_HOME)/etc/uvm-1.2/include/pureC \
		-I$(VCS_HOME)/etc/uvm-1.2/include \
		-DSNPS_REG_NOP -DSNPS_REG_DEBUG

LD	= gcc -lstdc++

.cpp.o:
	$(GCC) $*.cpp



all: a.out
	 	./a.out

a.out: main.o sys_driver.o 
	$(LD) -o a.out main.o sys_driver.o

main.o: \
	$(INCDIR)/regmodel/sys.h \
	$(INCDIR)/regmodel/comp1.h \
	$(INCDIR)/firmware/sys_driver.h

sys_driver.o: \
	$(INCDIR)/firmware/sys_driver.h \
	$(INCDIR)/firmware/sys_driver.cpp
	$(GCC) $(INCDIR)/firmware/sys_driver.cpp

clean:
	rm -rf *~ *.o a.out
