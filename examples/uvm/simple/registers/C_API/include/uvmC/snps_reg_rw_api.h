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
#include <string.h>

#include "svdpi.h"

#include "uints.h"


namespace snps_reg
{

    extern "C" {
        uint32 snps_reg__regRead(uint32 reg_id);
        void snps_reg__regWrite(uint32 reg_id, uint32 val);
        const char* snps_reg__get_context_name(int ctxt);
        void snps_reg__use_context_map(int ctxt);
    }

    typedef struct reg_map_id {
        uint32 reg_id;
        uint32 map_id;
    } reg_map_id;
    

    inline volatile uint32 regRead(struct reg_map_id addr)
    {
        snps_reg__use_context_map(addr.map_id);
        return (volatile uint32) snps_reg__regRead(addr.reg_id);
    };
    
    inline void regWrite(struct reg_map_id addr, uint32 val)
    {
        snps_reg__use_context_map(addr.map_id);
        snps_reg__regWrite(addr.reg_id, (uint32) val);
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
            : m_parent(parent),
            m_name(name),
            m_baseAddr(baseAddr)
        {}

        regmodel(int ctxt)
            : m_parent(0),
            m_name(m_get_context_name(ctxt)),
            m_baseAddr(ctxt)
        {}

            const char* const get_full_name()
            {
                static char full_name[4096];
                static char *p;
                
                if (m_parent == 0) p = full_name;
                else {
                    (void) m_parent->get_full_name();
                    *p++ = '.';
                }
                strcpy(p, m_name);
                p += strlen(m_name);
                *p = '\0';

                return full_name;
            }

    protected:
        regmodel *m_parent;
        const char* const m_name;
        const size_t m_baseAddr;

        void set_scope()
        {
            static svScope m_scp;
            
            if (m_scp == NULL)
                m_scp = svGetScopeFromName("$unit");
            svSetScope(m_scp);
        }

        const char* m_get_context_name(int ctxt)
        {
            set_scope();
            snps_reg__get_context_name(ctxt);
        }

        int get_context_id()
        {
            // Only the root has the context ID stored in the base address
            regmodel *rm = this;
            while (rm->m_parent) rm = rm->m_parent;
            return rm->m_baseAddr;
        }
    };

};


extern "C" {
    uint32 snps_reg__get_reg_id(const char* const path,
                                const char* const name);

    uint32 snps_reg__get_fld_id(const char* const path,
                                const char* const reg,
                                const char* const name);
}
extern "C" {
    uint32 snps_reg__regRead(uint32 reg_id);
    void snps_reg__regWrite(uint32 reg_id, uint32 val);
}


#define SNPS_REG_INIT_REG(_name)       __##_name##_id__(0)

#define SNPS_REG_ADDROF_REG(_type, _name, _offset)                      \
    private:                                                            \
    uint32 __##_name##_id__;                                            \
    public:                                                             \
    inline snps_reg::reg_map_id _name()                                 \
    {                                                                   \
        if (__##_name##_id__ == 0) {                                    \
            set_scope();                                                \
            __##_name##_id__ = snps_reg__get_reg_id(get_full_name(), #_name); \
        }                                                               \
        snps_reg::reg_map_id addr =                                     \
            {__##_name##_id__, get_context_id()};                       \
        return addr;                                                    \
    }

#define SNPS_REG_INIT_FLD(_rg, _name)  __##_rg##_##_name##_id__(0)

#define SNPS_REG_ADDROF_FLD(_type, _reg, _name, _offset)                \
    private:                                                            \
    uint32 __##_reg##_##_name##_id__;                                   \
    public:                                                             \
    inline snps_reg::reg_map_id _reg##_##_name()                        \
    {                                                                   \
        if (__##_reg##_##_name##_id__ == 0) {                           \
            set_scope();                                                \
            __##_reg##_##_name##_id__ = snps_reg__get_fld_id(get_full_name(), \
                                                             #_reg,     \
                                                             #_name);   \
        }                                                               \
        snps_reg::reg_map_id addr =                                     \
            {__##_reg##_##_name##_id__, get_context_id()};              \
        return addr;                                                    \
    }


#endif
