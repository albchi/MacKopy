//-------------------------------------------------------------
//    Copyright 2011 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary work of
// Synopsys, Inc., and is fully protected under copyright and trade
// secret laws. You may not view, use, disclose, copy, or distribute this
// file or any information contained herein except pursuant to a valid
// written license from Synopsys.
//
//-------------------------------------------------------------

#include "sys_driver.h"

using namespace snps_reg;

int
sys_driver::trivial(sys_t Sys)
{
    (void) regRead(Sys.Comp1a.regA());
    (void) regRead(Sys.Comp1a.regB_fldA());
    (void) regRead(Sys.Comp1b.regB_fldA());
    (void) regRead(Sys.Comp1b.regC());
    (void) regRead(Sys.Comp2.regA());
    (void) regRead(Sys.Comp2.rf1[0].r0());
    (void) regRead(Sys.Comp2.rf1[3].r1_fB());
    (void) regRead(Sys.Comp2.rf1[3].r2());
    (void) regRead(Sys.Comp2.regE());
    
    regWrite(Sys.Comp2.regE(), 0x1111);
    regWrite(Sys.Comp1a.regB(), 0x2222);
    regWrite(Sys.Comp1b.regC(), 0x3333);
    regWrite(Sys.Comp1b.regB_fldC(), 0x4444);
    regWrite(Sys.Comp2.rf1[3].r1_fA(), 0x5555);
    regWrite(Sys.Comp2.regE(), 0x1111);
    
    return 0;
};


int
sys_driver::comp1_drv(comp1_t dev)
{
unsigned int val;
/*
    (void) regRead(dev.regA());
    regWrite(dev.regB(), 0xFAFAFA);
*/
#ifdef SNPS_UVMC_ONLY
    //(void) regGet(dev.regA());
    //regSet(dev.regB(), 0xFAFAFA);
   val = regGet(dev.regA());
    printf("YYYYYYYYYYYYYYYYY");
    printf("dev.regA() = 0x%x\n", val);
    val = regGet(dev.regB());
    printf("dev.regB() = 0x%x\n", val);

    regSet(dev.regA(), 0xDEADBEEF);
    val = regGet(dev.regA());
    printf("dev.regA() = 0x%x\n", val);

    regSet(dev.regB(), 0xCAFE1234);
    val = regGet(dev.regB());
    printf("dev.regB() = 0x%x\n", val);



#endif
    return 0;
};

