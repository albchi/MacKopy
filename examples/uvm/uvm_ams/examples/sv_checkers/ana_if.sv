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
// Description : Shows how to group analog nodes in SV interface 
//
//-----------------------------------------------------------------------------

////////////////////////////////////////////////////////////
`ifndef __ANA_IF_SV
`define __ANA_IF_SV

interface ana_if(input bit clk);
  real vin;

  clocking mck @(negedge clk);
    default output #1;
    output vin;
  endclocking: mck


  clocking sck @(negedge clk);
    default input #1;
    input vin;
  endclocking: sck
    
  modport tb2dut(clocking mck);
  modport sample(clocking sck);
  modport async_sample(input clk, input vin);
 
endinterface: ana_if

`endif

