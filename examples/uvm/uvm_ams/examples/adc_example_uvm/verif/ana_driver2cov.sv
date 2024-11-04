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
// Description : Analog driver callback
//
//-----------------------------------------------------------------------------

`ifndef __ANA_DRIVER2COV_SV
`define __ANA_DRIVER2COV_SV

class ana_driver2cov extends ana_driver_callbacks;
  ana_cov cov;

  function new(ana_cov cov);
    this.cov = cov;
  endfunction

  virtual task post_trans(sv_ams_real vin);
    cov.cover_vals(vin);
  endtask
endclass
`endif

