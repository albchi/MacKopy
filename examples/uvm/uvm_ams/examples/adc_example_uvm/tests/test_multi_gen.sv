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
// Description : Show how to use Multi Gen to pick various source generators
//
//-----------------------------------------------------------------------------

class test_multi_gen extends ana_base_test;

  `uvm_component_utils(test_multi_gen)

  sv_ams_sawtooth_voltage_gen   vsaw_gen;
  sv_ams_rand_voltage_gen       vrand_gen;
  sv_ams_sine_voltage_gen       vsine_gen;

  function new(string name = "test_multi_gen", uvm_component parent =  null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    vsaw_gen = new;
    vsine_gen = new;
    vrand_gen = new;

    vsaw_gen.set_v_range(cfg.min_voltage.get_real(), cfg.max_voltage.get_real());
    vsaw_gen.set_frequency(cfg.frequency.get_real());
    vsine_gen.set_v_range(cfg.min_voltage.get_real(), cfg.max_voltage.get_real());
    vsine_gen.set_frequency(cfg.frequency.get_real());
    vrand_gen.set_v_range(cfg.min_voltage.get_real(), cfg.max_voltage.get_real()); 
  endfunction

  task run_phase(uvm_phase phase);
    ana_base_sequence  seq;

    super.run_phase(phase);

    phase.raise_objection(this);
    seq = ana_base_sequence::type_id::create("seq");

    for (int cnt = 0; cnt < this.cfg.num_trans; cnt++) begin
      if(cnt==0) seq.vin_gen = vsaw_gen; 
      else if(cnt==cfg.num_trans/3) seq.vin_gen = vsine_gen;
      else if(cnt==2*cfg.num_trans/3) seq.vin_gen = vrand_gen;

      seq.start(env.agent.seqr);
    end
    phase.drop_objection(this);
  endtask
endclass 

