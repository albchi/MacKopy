//-----------------------------------------------------------------------------
// This confidential and proprietary software may be used only as authorized
// by a licensing agreement from Synopsys Inc. In the event of publication,
// the following notice is applicable:
//
// (C) COPYRIGHT 2013 SYNOPSYS INC.  ALL RIGHTS RESERVED
//
// The entire notice above must be reproduced on all authorized copies.
//-----------------------------------------------------------------------------
//
// UVM-AMS Top File
//
//-----------------------------------------------------------------------------

`ifndef __UVM_AMS_SV
`define __UVM_AMS_SV

`ifndef  UVM_PKG_SV
`include "uvm_pkg.sv"  	// DO NOT INLINE
`endif
  
import uvm_pkg::*; 

`include "sv_ams_math.sv"
`include "sv_ams_if.sv"
`include "sv_ams_real.sv"
`include "sv_ams_voltage_gen.sv"
`include "sv_ams_checkers.sv"
`include "sv_ams_version.sv"

`ifdef SVA_AMS_CHECKERS
`include "sva_ams_checkers.sv"
`endif

`endif
