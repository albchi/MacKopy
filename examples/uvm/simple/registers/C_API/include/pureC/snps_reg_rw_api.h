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


#ifndef __SNPS_REG__H__
#define __SNPS_REG__H__

#include <stdio.h>

#include "uints.h"


namespace snps_reg
{
    inline volatile uint8  regRead(volatile uint8  *addr)
    {
#ifdef SNPS_REG_DEBUG
        printf("Reading uint8 from 0x%08x...\n", addr);
#endif
#ifndef SNPS_REG_NOP
        return *addr;
#endif
    };
    
    inline volatile uint16 regRead(volatile uint16 *addr)
    {
#ifdef SNPS_REG_DEBUG
        printf("Reading uint16 from 0x%08x...\n", addr);
#endif
#ifndef SNPS_REG_NOP
        return *addr;
#endif
    };
    
    inline volatile uint32 regRead(volatile uint32 *addr)
    {
#ifdef SNPS_REG_DEBUG
        printf("Reading uint32 from 0x%08x...\n", addr);
#endif
#ifndef SNPS_REG_NOP
        return *addr;
#endif
    };
    

    inline void regWrite(volatile uint8  *addr, uint8  val)
    {
#ifdef SNPS_REG_DEBUG
        printf("Writing uint8 0x%08x to 0x%08x...\n", val, addr);
#endif
#ifndef SNPS_REG_NOP
        (*addr) = val;
#endif
    };
    
    inline void regWrite(volatile uint16 *addr, uint16 val)
    {
#ifdef SNPS_REG_DEBUG
        printf("Writing uint16 0x%08x to 0x%08x...\n", val, addr);
#endif
#ifndef SNPS_REG_NOP
        (*addr) = val;
#endif
    };

    inline void regWrite(volatile uint32 *addr, uint32 val)
    {
#ifdef SNPS_REG_DEBUG
        printf("Writing uint32 0x%08x to 0x%08x...\n", val, addr);
#endif
#ifndef SNPS_REG_NOP
        (*addr) = val;
#endif
    };


//
// The following are implementation-specific and should not be used
// directly in user code.
//

    
    class regmodel {

    public:
        regmodel(regmodel *parent,
                 const char* const name,
                 size_t baseAddr)
            : m_baseAddr(baseAddr)
        {}
        
        regmodel(int ctxt)
            : m_baseAddr(0)
        {}
        
    protected:
       const size_t m_baseAddr;
    };
};



#define SNPS_REG_INIT_REG(_name)       __##_name##_id__(0)

#define SNPS_REG_ADDROF_REG(_type, _name, _offset)                      \
    private:                                                            \
    uint32 __##_name##_id__;                                            \
    public:                                                             \
    inline volatile _type *_name()                                      \
    {                                                                   \
        return reinterpret_cast<volatile _type*>(m_baseAddr + _offset); \
    }

#define SNPS_REG_INIT_FLD(_rg, _name)  __##_rg##_##_name##_id__(0)

#define SNPS_REG_ADDROF_FLD(_type, _reg, _name, _offset)                \
    private:                                                            \
    long __##_reg##_##_name##_id__;                                     \
    public:                                                             \
    inline volatile _type *_reg##_##_name()                             \
    {                                                                   \
        return reinterpret_cast<volatile _type*>(m_baseAddr + _offset); \
    }

#endif
