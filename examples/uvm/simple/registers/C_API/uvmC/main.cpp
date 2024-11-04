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

#include "regmodel/ral_sys.h"
#include "firmware/sys_driver.h"

//
// This is the entry point from SV back into C code
//
extern "C" int
comp1_drv(int context)
{
    comp1_t dev(context);
    return sys_driver::comp1_drv(dev);
}
