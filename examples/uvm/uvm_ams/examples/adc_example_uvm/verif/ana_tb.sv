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
// Description : Testbench top level
//
//-----------------------------------------------------------------------------
`include "uvm_ams.sv"
`include "ana_comp_if.sv"

////////////////////////////////////////////////////////////
`ifdef NO_VERILOG_WRAPPER
`else
module A2DConverter(input real in, input real s, output real o1, output real o2, output real o3, output real o4);
endmodule
`endif

////////////////////////////////////////////////////////////
module tb;
  logic clk=1'b0;
  ana_comp_if ana_if(clk);
  ams_src_if ams_if(clk);

  `include "tests.svh"

  A2DConverter DUT(ana_if.vin, ana_if.s, ana_if.o1, ana_if.o2, ana_if.o3, ana_if.o4);
   
  always #10 clk = ~clk;

  initial begin
    $vcdpluson;
    uvm_config_db#(virtual ana_comp_if )::set(uvm_root::get(),"*", "ana_vif", ana_if);
    run_test();
  end

`ifdef SVA_AMS
  always@(cross(DUT.sclk1-0.9,+1))
    $display("Clk1 Posedge");
`endif
  
`ifdef SVA_AMS_EXT
  always @(negedge clk)
    check_o: assert (DUT.o1 <= 1.8);
`endif
    
endmodule


`ifdef SVA_AMS_EXT
module anaComparatorChecker(vin, vref, gt, clk);
input vin, vref, gt, clk;
wreal vin, vref, gt;
bit clk;

   always @(negedge clk) begin
        if ($time > 25) begin
            assert (((gt > 0.9) && (vin > vref))||((gt < 0.9) && (vref > vin)))
`ifdef DISPLAY_PASSES
                $display($time,,,
                "Analog Comparator (%m) PASSED: vin=%g, vref=%g, gt=%g\n",
                vin, vref, gt);
`endif
            else begin
                $display($time,,,
                "Analog Comparator (%m) Malfunction: vin=%g, vref=%g, gt=%g\n", vin, vref, gt);
            end
        end
        
   end

AP: assert property (@(negedge clk)
	(($time >25) && (gt > 0.9) |-> 
		(1, $display("[%0d] gt>0.9 vref %g, vin %g, vref<vin %b", 
						$time, vref, vin, vref<vin)) ##0 
		(vin > vref))
	and 
	(($time >25) && (gt < 0.9) |-> 
		(1, $display("[%0d] gt<0.9 vref %g, vin %g, vref>vin %b", 
						$time, vref, vin, vref>vin)) ##0 
		(vref > vin))
)
`ifdef DISPLAY_PASSES
       $display($time,,,
                "Analog Comparator (%m) PASSED: vin=%g, vref=%g, gt=%g\n",
                vin, vref, gt);
`endif
 else begin
      $display($time,,,
               "Analog Comparator (%m) Malfunction: vin=%g, vref=%g, gt=%g\n", 
				vin, vref, gt);
      end
endmodule
`endif
