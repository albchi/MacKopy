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
// Description : Test showing how to inject a ramp with noise
//
//-----------------------------------------------------------------------------

class test_ramp extends ana_base_test;
  `uvm_component_utils(test_ramp)

   sv_ams_rand_voltage_gen  rand_gen;
   ana_base_sequence  seq;
   real quantum = 0.1;
   real threshold = 0.010; // 10mV
   int delta = 0;

  function new(string name = "test_ramp", uvm_component parent =  null);
    super.new(name, parent);
    cfg.num_trans = 160;
    rand_gen = new;
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    phase.raise_objection(this);
    seq = new("seq");
    seq.vin_gen = rand_gen;

    for(int cnt = 0; cnt < cfg.num_trans; cnt++) begin
      if(cnt % 10 == 0) begin
       delta++;
       seq.vin_gen.set_v_range((delta*quantum)-threshold, (delta*quantum)+threshold);
      end 
      seq.start(env.agent.seqr);
    end
    phase.drop_objection(this);
  endtask
endclass

