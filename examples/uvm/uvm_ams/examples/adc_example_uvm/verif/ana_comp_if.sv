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
`ifndef __ANA_COMP_IF_SV
`define __ANA_COMP_IF_SV

interface ana_comp_if(input bit clk);
  real vin;
  real s;
  real strb;
  real o1, o2, o3, o4;

  clocking mck @(negedge clk);
    default output #1;
    output vin;
    output s;
    input o1;
    input o2;
    input o3;
    input o4;
  endclocking: mck


  clocking sck @(negedge clk);
    default input #1;
    input vin;
    input s;
    input o1;
    input o2;
    input o3;
    input o4;
  endclocking: sck
    
  modport tb2dut(clocking mck);
  modport sample(clocking sck);
  modport async_sample(input clk,
                       input vin,
                       input s, 
                       input o1, 
                       input o2, 
                       input o3, 
                       input o4);

 
`ifdef SVA_AMS
  property check_o;
    @(negedge clk) (o1 <= 1.8);
  endproperty
`endif
  
endinterface: ana_comp_if

`endif

