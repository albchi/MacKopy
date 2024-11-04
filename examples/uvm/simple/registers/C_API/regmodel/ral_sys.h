#ifndef __RAL_SYS_H__
#define __RAL_SYS_H__


#include <stdlib.h>
#include "snps_reg_rw_api.h"
#include "ral_comp1.h"
#include "ral_comp1.h"
#include "ral_comp2.h"
class sys_t : public snps_reg::regmodel {

  public:

  comp1_t Comp1a;
  comp1_t Comp1b;
  comp2_t Comp2;

  sys_t(const char* const name,
	size_t baseAddr,
	snps_reg::regmodel *parent = 0)
	: regmodel(parent, name, baseAddr),
    Comp1a("Comp1a", baseAddr+0x1A0000, this),
    Comp1b("Comp1b", baseAddr+0x1B0000, this),
    Comp2("Comp2", baseAddr+0x200000, this)
  {}

  sys_t(int ctxt)
    : regmodel(ctxt),
    Comp1a("Comp1a", 0, this),
    Comp1b("Comp1b", 0, this),
    Comp2("Comp2", 0, this)
  {}
};
#endif
