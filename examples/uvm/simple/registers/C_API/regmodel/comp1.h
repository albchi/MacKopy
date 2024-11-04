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

//
// The content of this file is normally generated by ralgen
//


#ifndef __COMP1__H__
#define __COMP1__H__

#include <stdlib.h>

#include "snps_reg_rw_api.h"

class comp1_t : public snps_reg::regmodel
{
    public:

    SNPS_REG_ADDROF_REG(uint32, regA, 0x00);
    SNPS_REG_ADDROF_REG(uint32, regB, 0x04);
    SNPS_REG_ADDROF_FLD(uint8,  regB, fldA, 0x04);
    SNPS_REG_ADDROF_FLD(uint8,  regB, fldB, 0x05);
    SNPS_REG_ADDROF_FLD(uint16, regB, fldC, 0x06);
    SNPS_REG_ADDROF_REG(uint32, regC, 0x08);

    comp1_t(const char* const name,
            size_t baseAddr,
            snps_reg::regmodel *parent = 0)
        : regmodel(parent, name, baseAddr),
        SNPS_REG_INIT_REG(regA),
        SNPS_REG_INIT_REG(regB),
        SNPS_REG_INIT_FLD(regB, fldA),
        SNPS_REG_INIT_FLD(regB, fldB),
        SNPS_REG_INIT_FLD(regB, fldC),
        SNPS_REG_INIT_REG(regC)
    {}

    comp1_t(int ctxt)
        : regmodel(ctxt),
        SNPS_REG_INIT_REG(regA),
        SNPS_REG_INIT_REG(regB),
        SNPS_REG_INIT_FLD(regB, fldA),
        SNPS_REG_INIT_FLD(regB, fldB),
        SNPS_REG_INIT_FLD(regB, fldC),
        SNPS_REG_INIT_REG(regC)
    {}
};

#endif
