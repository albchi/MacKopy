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

class slew_checker_test extends uvm_test;
  `uvm_component_utils(slew_checker_test)
  
  sv_ams_slew_checker #( 0.05, 0) pos_chk;
  sv_ams_slew_checker #(0.05,1) neg_chk;

  function new(string name = "slew_checker_test", uvm_component parent = null);
    super.new(name, parent);
    pos_chk = new("pos_chk", this);
    neg_chk = new("neg_chk", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    phase.raise_objection(this);
    
     pos_chk.started = 1;
     neg_chk.started = 1;

     #1_000
     pos_chk.started = 0;

     #1_000
     neg_chk.started = 0;

     #1_000
     pos_chk.set_params(0.01,+1);
     pos_chk.started = 1;

     #1_000
     pos_chk.started = 0;
     neg_chk.set_params(0.01,-1);
     neg_chk.started = 1;

     #1_000;

    phase.drop_objection(this);
  endtask
endclass

module top;
  logic clk=1'b0;
  sv_ams_sawtooth_voltage_gen #(-1.0, 1.0, 1.0E6) sawtooth=new; // 1.0V to 1.0V, 1MHz
  ams_src_if ana_if(clk);

  always #10 clk = ~clk;

  always @(posedge clk) begin
    ana_if.v = sawtooth.get_voltage();
  end

  initial begin 
     $vcdpluson;
     uvm_resource_db#(virtual ams_src_if)::set("*", "uvm_ams_src_if", ana_if, null);
     run_test();
  
/*
     if(pos_chk.log.get_message_count(vmm_log::WARNING_SEV) != 1)
       `uvm_error(pos_chk.log, "Wrong number of Warnings");
                                                               
     if(neg_chk.log.get_message_count(vmm_log::WARNING_SEV) != 4)
       `vmm_error(neg_chk.log, "Wrong number of Warnings");
*/
     //pos_chk.log.report();
     //$finish;
  end

endmodule

