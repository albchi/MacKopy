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
// Real Number Modeling
//
//-----------------------------------------------------------------------------

`include "uvm_ams.sv" 

module top;
  real in, out;
  logic sample=0;
  amp#(2.50) dut(in, out);
  sv_ams_sine_voltage_gen #(-1.0, +1.0, 1.0E6)sine =new; 

  always #5 sample = ~sample;

  always @(posedge sample) begin
    in = sine.get_voltage();
    #1 $display("In=%2.2f - Out=%2.2f", in, out);
  end

  initial begin
    #1_000 $finish;
  end
  
endmodule

