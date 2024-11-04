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

`include "uvm_ams.sv"

class stability_checker_test extends uvm_test;
  `uvm_component_utils(stability_checker_test)
  
  sv_ams_stability_checker#(1.5,0.05) chk;

  function new(string name = "stability_checker_test", uvm_component parent = null);
    super.new(name, parent);
    chk = new("chk",this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    
     chk.started = 1;

     #1_000
     chk.started = 0;

     #1_000
     chk.set_params(1.45,0.05);
     chk.started = 1;

     #1_000
    phase.drop_objection(this);
  endtask
endclass

module top;
  logic clk=1'b0;
  ams_src_if ana_if(clk);

  sv_ams_sawtooth_voltage_gen #(1.4, 1.6, 1.0E6)sawtooth=new; // 0 to 1.8V, 1MHz
  always #10 clk = ~clk;

  initial begin 
     $vcdpluson;
     uvm_resource_db#(virtual ams_src_if)::set("*", "uvm_ams_src_if", ana_if, null);
     run_test();
  end

  always @(posedge clk) begin
    ana_if.v = sawtooth.get_voltage();
  end
endmodule

