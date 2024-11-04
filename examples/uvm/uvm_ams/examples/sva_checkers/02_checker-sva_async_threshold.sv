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
// Description : Basic testbench
//
//-----------------------------------------------------------------------------

`define SVA_AMS_CHECKERS
`include "ana_if.sv"
`include "uvm_ams.sv"

module top;
  logic clk=1'b0;
  ana_if ana_if(clk);

  sv_ams_sine_voltage_gen #(-1.8, 1.8, 1.0E6) sine = new; // 0 to 1.8V, 1MHz
  ams_async_threshold_checker #(.threshold(1.7), .in_out(1)) async_rising_thr_chk (.vin(ana_if.vin));
  ams_async_threshold_checker #(.threshold(-1.7), .in_out(0)) async_falling_thr_chk (.vin(ana_if.vin));

  always #10 clk = ~clk;

  initial begin 
    $vcdpluson;
    #1_000 $finish;
  end

  always @(posedge clk) begin
    ana_if.vin = sine.get_voltage();
  end
endmodule

