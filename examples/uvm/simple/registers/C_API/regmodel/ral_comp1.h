#ifndef __RAL_COMP1_H__
#define __RAL_COMP1_H__


#include <stdlib.h>
#include "snps_reg_rw_api.h"
class comp1_t : public snps_reg::regmodel {

  public:

  SNPS_REG_ADDROF_REG(uint32, regA, 0x0);
  SNPS_REG_ADDROF_REG(uint32, regB, 0x4);
  SNPS_REG_ADDROF_FLD(uint8, regB, fldA, 0x4+0);
  SNPS_REG_ADDROF_FLD(uint8, regB, fldB, 0x4+1);
  SNPS_REG_ADDROF_FLD(uint16, regB, fldC, 0x4+2);
  SNPS_REG_ADDROF_REG(uint32, regC, 0x8);

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
