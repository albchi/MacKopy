#ifndef __RAL_COMP2_H__
#define __RAL_COMP2_H__


#include <stdlib.h>
#include "snps_reg_rw_api.h"
class comp2_t : public snps_reg::regmodel {

  public:

class rf1_t : public snps_reg::regmodel {

  public:

  SNPS_REG_ADDROF_REG(uint32, r0, 0x0);
  SNPS_REG_ADDROF_REG(uint32, r1, 0x4);
  SNPS_REG_ADDROF_FLD(uint16, r1, fA, 0x0+0);
  SNPS_REG_ADDROF_FLD(uint16, r1, fB, 0x0+2);
  SNPS_REG_ADDROF_REG(uint32, r2, 0x8);

  rf1_t(const char* const name, size_t baseAddr, snps_reg::regmodel *parent = 0)
    : regmodel(parent, name, baseAddr),
  SNPS_REG_INIT_REG(r0),
  SNPS_REG_INIT_REG(r1),
  SNPS_REG_INIT_FLD(r1, fA),
  SNPS_REG_INIT_FLD(r1, fB),
  SNPS_REG_INIT_REG(r2)
  {}

  rf1_t(int ctxt)
    : regmodel(ctxt),
  SNPS_REG_INIT_REG(r0),
  SNPS_REG_INIT_REG(r1),
  SNPS_REG_INIT_FLD(r1, fA),
  SNPS_REG_INIT_FLD(r1, fB),
  SNPS_REG_INIT_REG(r2)
  {}

};

  SNPS_REG_ADDROF_REG(uint32, regA, 0x0);
  rf1_t rf1[4];
  SNPS_REG_ADDROF_REG(uint32, regE, 0x1F0);

  comp2_t(const char* const name,
	size_t baseAddr,
	snps_reg::regmodel *parent = 0)
	: regmodel(parent, name, baseAddr),
  SNPS_REG_INIT_REG(regA),
  rf1((rf1_t[4]){  rf1_t("rf1[0]", baseAddr+0x100+0x0*0x10, this),
  rf1_t("rf1[1]", baseAddr+0x100+0x1*0x10, this),
  rf1_t("rf1[2]", baseAddr+0x100+0x2*0x10, this),
  rf1_t("rf1[3]", baseAddr+0x100+0x3*0x10, this)}),
  SNPS_REG_INIT_REG(regE)
  {}

  comp2_t(int ctxt)
    : regmodel(ctxt),
  SNPS_REG_INIT_REG(regA),
  rf1((rf1_t[4]){  rf1_t("rf1[0]", 0, this),
  rf1_t("rf1[1]", 0, this),
  rf1_t("rf1[2]", 0, this),
  rf1_t("rf1[3]", 0, this)}),
  SNPS_REG_INIT_REG(regE)
  {}

};

#endif
