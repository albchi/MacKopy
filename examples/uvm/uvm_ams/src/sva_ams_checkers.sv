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
// Title: SVA AMS Checkers
//
//-----------------------------------------------------------------------------

////////////////////////////////////////////////////////////
`ifndef _UVM_AMS_CHECKER_SV_
`define _UVM_AMS_CHECKER_SV_

////////////////////////////////////////////////////////////
// Module: ams_sync_threshold_checker
//   This module checks on each positive of *clk* that a given signal
//   *vin* doesn't go above/below a pre-defined threshold.
//   The signal comparison and threshold are defined with
//   the parameters *threshold* and *in_out*
//
// _Definition_
// | 	module ams_sync_threshold_checker(clk,vin);
//
// _Arguments_
//  - input bit *clk*
//  - input real *vin*
//  - parameter real *threshold* = 0.0 (in V)
//  - parameter bit *in_out* = 1 (+1: high, 0: low)
//      0 indicates that the analog signal should always remain 
//        *below* *threshold*
//      1 indicates that the analog signal should always remain 
//        *above* *threshold*
//
// The following example shows how to instantiate two <ams_sync_threshold_checker>
// objects to verify that *vin* doesn't fall below 1.6V or rise above 1.7V.
//   
// (start code)
//module top;
//  logic clk=1'b0;
//  real  vin;
//
//  ams_sync_threshold_checker #(.threshold(1.7), .in_out(0)) 
//          sync_below_chk (.clk(clk), .vin(vin));
//  ams_sync_threshold_checker #(.threshold(1.6), .in_out(1)) 
//         sync_above_chk (.clk(clk), .vin(vin));
//
//  always #10 clk = ~clk;
//
//endmodule
// (end code)

module ams_sync_threshold_checker(clk,vin);
  input bit clk;
  input real vin;
  parameter real threshold = 0.0;
  parameter bit in_out = 1;

  property below;
    @(posedge clk) disable iff(in_out != 0)
      vin <= threshold;
  endproperty

  property above;
    @(posedge clk) disable iff(in_out != 1)
      vin >= threshold;
  endproperty

  check_b: 
     assert property (below) 
     else $display("\tvin=%0.3f is not <= threshold=%0.3f", vin, threshold);

  check_a: 
     assert property (above) 
     else $display("\tvin=%0.3f is not >= threshold=%0.3f", vin, threshold);
endmodule

////////////////////////////////////////////////////////////
// Module: ams_async_threshold_checker
//   This module asynchronously checks that a given signal
//   *vin* doesn't go above/below a pre-defined threshold.
//   The signal comparison and threshold are defined with
//   the parameters *threshold* and *in_out*
//
// _Definition_
// | 	module ams_async_threshold_checker(clk,vin);
//
// _Arguments_
//  - input bit *clk*
//  - input real *vin*
//  - parameter real *threshold* = 0.0 (in V)
//  - parameter bit *in_out* = 1 (+1: high, 0: low)
//      0 indicates that the analog signal should always remain 
//        *below* *threshold*
//      1 indicates that the analog signal should always remain 
//        *above* *threshold*
//
// The following example shows how to instantiate two <ams_async_threshold_checker>
// objects to verify that *vin* doesn't fall below 1.6V or rise above 1.7V.
//   
// (start code)
//module top;
//  logic clk=1'b0;
//  real  vin;
//
//  ams_async_threshold_checker #(.threshold(1.7), .in_out(0)) 
//          async_below_chk (.vin(vin));
//  ams_async_threshold_checker #(.threshold(1.6), .in_out(1)) 
//         async_above_chk (.vin(vin));
//
//endmodule
// (end code)

module ams_async_threshold_checker(vin);
  input real vin;
  parameter real threshold = 0.0;
  parameter bit in_out = 1;

 always @(vin) begin
    if(in_out == 0)
      check_min:assert (vin <= threshold) 
      else $display("\tvin=%0.3f is not <= threshold=%0.3f", vin, threshold);
    else
      check_max:assert (vin >= threshold) 
      else $display("\tvin=%0.3f is not >= threshold=%0.3f", vin, threshold);
    end
endmodule

////////////////////////////////////////////////////////////
// Module: ams_sync_window_checker
//   This module checks on each positive of *clk* that a given signal
//   *vin* remains in or out a given voltage window.
//   The voltage window is defined with *threshold_lo* and *threshold_hi* 
//  parameters.
//   The in/out comparison in_out is defined with *in_out* parameter.
//
// _Definition_
// | 	module ams_sync_window_checker(clk,vin);
//
// _Arguments_
//  - input bit *clk*
//  - input real *vin*
//  - parameter real *threshold_lo* = 0.0 (in V)
//  - parameter real *threshold_hi* = 1.0 (in V)
//  - parameter integer *in_out* = 1 (0: in window, 1: out of window)
//
// The following example shows how to instantiate an <ams_sync_window_checker>
// objects to verify that *vin* remains between 0.0V 1.2V.
//   
// (start code)
//module top;
//  logic clk=1'b0;
//  real  vin;
//
//  ams_sync_window_checker #(.threshold_lo(0.0),
//                            .threshold_hi(+1)) 
//                            .in_out(+1)) 
//          sync_win_chk(.clk(clk), .vin(vin));
//endmodule
// (end code)

module ams_sync_window_checker(clk, vin);
  input bit clk;
  input real vin;
  parameter real threshold_lo = 0.0;
  parameter real threshold_hi = 1.0;
  parameter bit in_out = 1;  // 0: in window, 1: out of window

  property in;
    @(posedge clk) disable iff(in_out != 0)
      vin > threshold_lo && vin < threshold_hi;
  endproperty

  property out;
    @(posedge clk) disable iff(in_out != 1)
      vin < threshold_lo || vin > threshold_hi;
  endproperty

  check_in: 
     assert property (in) 
     else $display("\tvin=%0.3f is not within [%0.3f-%0.3f]", vin, threshold_lo, threshold_hi);
  check_out: 
     assert property (out) 
     else $display("\tvin=%0.3f is within [%0.3f-%0.3f]", vin, threshold_lo, threshold_hi);
endmodule

////////////////////////////////////////////////////////////
// Module: ams_async_window_checker
//   This module asynchonously checks that a given signal
//   *vin* remains in or out a given voltage window.
//   The voltage window is defined with *threshold_lo* and *threshold_hi* 
//  parameters.
//   The in/out comparison in_out is defined with *in_out* parameter.
//
// _Definition_
// | 	module ams_async_window_checker(vin);
//
// _Arguments_
//  - input real *vin*
//  - parameter real *threshold_lo* = 0.0 (in V)
//  - parameter real *threshold_hi* = 1.0 (in V)
//  - parameter integer *in_out* = 1 (0: in window, 1: out of window)
//
// The following example shows how to instantiate an <ams_async_window_checker>
// objects to verify that *vin* remains between 0.0V 1.2V.
//   
// (start code)
//module top;
//  logic clk=1'b0;
//  real  vin;
//
//  ams_async_window_checker #(.threshold_lo(0.0),
//                             .threshold_hi(+1)) 
//                             .in_out(1)) 
//          async_win_chk(.vin(vin));
//endmodule
// (end code)

module ams_async_window_checker(vin);
  input real vin;
  parameter real threshold_lo = 0.0;
  parameter real threshold_hi = 1.0;
  parameter bit in_out = 1;  // 0: in window, 1: out of window

  always @(vin) begin
    if(in_out==0)
       check_in:assert (vin >= threshold_lo && vin <= threshold_hi)
       else $display("\tvin=%0.3f is not within [%0.3f-%0.3f]", vin, threshold_lo, threshold_hi);

    else
       check_out:assert (vin < threshold_lo || vin > threshold_hi)
       else $display("\tvin=%0.3f is within [%0.3f-%0.3f]", vin, threshold_lo, threshold_hi);
  end
endmodule

////////////////////////////////////////
// Module: ams_sync_stability_checker
//   This module checks on each positive of *clk* that a given signal
// *vin* is stable (*vref* +/- *tolerance*) when *enable* is asserted
//
// _Definition_
// | 	module ams_sync_stability_checker(clk, vin, enable)
//
// _Arguments_
//  - input bit  *clk*
//  - input real *vin*
//  - input bit  *enable*
//  - parameter real *tolerance* = 0.01 (1%)
//  - parameter real *vref* = 0.0 (0V)
//
// The following example shows how to instantiate an <ams_sync_stability_checker>
// objects to verify that *vin* remains equal to 1.0V +/- 5%
//   
// (start code)
//module top;
//  logic clk=1'b0;
//  logic ena=1'b1;
//  real  vin;
//
//  ams_sync_stability_checker #(.vref(1.0), .tolerance(0.05))
//          sync_stable(.clk(clk), .ena(ena), .vin(vin));
//endmodule
// (end code)

module ams_sync_stability_checker(clk, vin, enable);
  input bit clk;			// clock
  input real vin;              		// Analog input
  input bit enable;			// enable input comparison
  parameter real tolerance=0.01; 	// default tolerance=1%
  parameter real vref=0.0;		// reference value

  property p;
  @(posedge clk) disable iff (!enable)
                 (vin >= (1-tolerance)*vref && vin <= (1+tolerance)*vref);
  endproperty
  ams_sync_stability_checker: 
     assert property (p) 
     else $display("\tvin=%0.3f vref=%0.3f +/-%0.3f", vin, vref, tolerance);
endmodule

////////////////////////////////////////
// Module: ams_sync_frame_checker
//   This module checks on each positive of *clk* that a given signal
// *vin* is stable (*vref* +/- *tolerance*) during a time window.
//
// _Definition_
// | 	module ams_sync_frame_checker(clk, vin, enable)
//
// _Arguments_
//  - input bit  *clk*
//  - input real *vin*
//  - input bit  *enable*
//  - parameter real *tolerance* = 0.01 (1%)
//  - parameter real *vref* = 0.0 (0V)
//  - parameter time *window_low* = 0  (module time precision)
//  - parameter time *window_high* = 0 (module time precision)
//
// The following example shows how to instantiate an <ams_sync_frame_checker>
// objects to verify that *vin* remains equalt to 1.0V +/- 5% from 10ns to 500ns
//   
// (start code)
//`timescale 1ns/1ps
//module top;
//  logic clk=1'b0;
//  logic ena=1'b1;
//  real  vin;
//
//  ams_sync_frame_checker #(.vref(1.0), .tolerance(0.05))
//                           .window_low(10), .window_hi(500))
//          sync_stable(.clk(clk), .ena(ena), .vin(vin));
//endmodule
// (end code)

module ams_sync_frame_checker(clk, vin, enable);
  input bit clk;			// clock
  input real vin;
  input bit enable;			// enable input comparison
  parameter real vref=0.0;		// reference value
  parameter real tolerance=0.01; 	// default tolerance=1%
  parameter time window_low = 0; 	// Window start time 
  parameter time window_high = 0; 	// Window end time

  bit ena = 1'b0;

  always @(posedge clk) begin
    ena <= enable && ($time >= window_low && $time <= window_high);
  end
  
  property p;
  @(posedge clk) disable iff (!ena)
                 (vin >= (1-tolerance)*vref && vin <= (1+tolerance)*vref);
  endproperty
  ams_sync_frame_checker: 
     assert property (p) 
     else $display("\tvin=%0.3f vref=%0.3f +/-%0.3f", vin, vref, tolerance);
endmodule

////////////////////////////////////////
// Module: ams_async_slew_checker
//   This module asynchronously checks that a given signal
//   steadily rises or falls above or below a pre-defined slew rate.
//   The slew rate and above/below checks are defined with
//   the *SLEW* and *IN_OUT* parameters
//
// _Definition_
// | 	module ams_async_slew_checker(clk, vin)
//
// _Arguments_
//  - input bit  *clk*
//  - input real *vin*
//  - parameter bit in_out 
// 	0: Indicates that slew rate is always *below* *SLEW*
// 	1: Indicates that slew rate is always *above* *SLEW*
//  - parameter real *slew* = 0.1 (100mV/ timescale)
//
// The following example shows how to instantiate an <ams_async_slew_checker>
// object to verify that *vin* rises with a slew rate of more than 10V/ns
//   
// (start code)
//`timescale 1ns/1ps
//module top;
//  logic clk=1'b0;
//  real  vin;
//
//  ams_async_slew_checker #(.in_out(+1), .tolerance(10.0))
//          sync_stable(.clk(clk), .vin(vin));
//endmodule
// (end code)
module ams_async_slew_checker(clk, vin);
  input bit clk;
  input real vin;
  parameter bit in_out = 1; // 0: below, 1: above
  parameter real slew=0.10; // default slew=100mV/timescale

  real vref = 0.0;
  real vref_d = 0.0;

  always @(posedge clk) begin
    vref_d <= vin;
    vref <= vref_d;
  end

  property below;
    @(posedge clk) disable iff (in_out != 0)
      fabs(vin-vref) < slew;
  endproperty

   property above;
    @(posedge clk) disable iff (in_out != 1)
      fabs(vin-vref) > slew;
  endproperty

  check_a:assert property (above)
     else $display("\tvin=%0.3f - vref=%0.3f is not < slew=%0.3f", vin, vref, slew);
  check_b:assert property (below)
     else $display("\tvin=%0.3f - vref=%0.3f is not > slew=%0.3f", vin, vref, slew);

endmodule

////////////////////////////////////////
// Module: ams_async_slew_checker_window
//   This module asynchronously checks that a given signal
// *vin* is steadily rising or falling within a given tolerance.
// It can enabled with *enable* signal.
//
// _Definition_
// | 	module ams_async_slew_checker_window(clk, vin, enable)
//
// _Arguments_
//  - input bit  *clk*
//  - input real *vin*
//  - input bit  *enable*
//  - parameter integer *direction* = 1 (0: falling, +1: rising)
//  - parameter real *tolerance* = 0.01 (1%)
//
// The following example shows how to instantiate an <ams_async_slew_checker_window>
// object to verify that *vin* rises with a slew rate of 10V/ns
//   
// (start code)
//`timescale 1ns/1ps
//module top;
//  logic clk=1'b0;
//  real  vin;
//
//  ams_async_slew_checker_window #(.direction(+1), .tolerance(10.0))
//          sync_stable(.clk(clk), .vin(vin));
//endmodule
// (end code)

module ams_async_slew_checker_window(clk, vin, enable);
  input bit clk;	// synchronous clock
  input real vin;  	// analog input
  input bit enable;	// enable window check when true 
  parameter bit in_out = 1; // 0: below, 1: above
  parameter real slew=0.10; // default slew=100mV/timescale

  real vref = 0.0;
  real vref_d = 0.0;

  always @(posedge clk) begin
    vref_d <= vin;
    vref <= vref_d;
  end

  property below;
    @(posedge clk) disable iff (in_out != 0 && !enable)
      fabs(vin-vref) < slew;
  endproperty

   property above;
    @(posedge clk) disable iff (in_out != 1 && !enable)
      fabs(vin-vref) > slew;
  endproperty

  check_a:assert property (above)
     else $display("\tvin=%0.3f - vref=%0.3f is not < slew=%0.3f", vin, vref, slew);
  check_b:assert property (below)
     else $display("\tvin=%0.3f - vref=%0.3f is not > slew=%0.3f", vin, vref, slew);

endmodule

`endif
