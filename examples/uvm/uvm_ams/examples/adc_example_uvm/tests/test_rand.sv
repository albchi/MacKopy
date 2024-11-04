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
// Description : Full random test
//
//-----------------------------------------------------------------------------


class ana_rand_sequence extends uvm_sequence#(sv_ams_real);

  `uvm_object_utils(ana_rand_sequence)

  sv_ams_generic_src       vin_gen;
  ana_cfg cfg;

  function new(string name = "ana_rand_sequence");
    super.new(name);
    void'(uvm_resource_db#(ana_cfg)::read_by_name(get_type_name(),  "ana_cfg", cfg));
  endfunction

  virtual task pre_body();
    super.pre_body();
    if(starting_phase != null) 
      starting_phase.raise_objection(this);
  endtask

  virtual task post_body();
    super.post_body();
    if(starting_phase != null) 
      starting_phase.drop_objection(this);
  endtask

  task body();
    for (int cnt = 0; cnt < cfg.num_trans; cnt++) begin
      `uvm_create(req);
      vin_gen.get_voltage;
      req = vin_gen.v;
      `uvm_send(req);
    end
  endtask
endclass

class test_rand extends ana_base_test;
  `uvm_component_utils(test_rand)

  sv_ams_rand_voltage_gen       rand_gen;
  ana_rand_sequence   seq;

  function new(string name = "test_mss", uvm_component parent =  null);
   super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rand_gen = new;
    rand_gen.set_v_range(cfg.min_voltage.get_real(), cfg.max_voltage.get_real());
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    seq = new("ana_rand_seq");
    seq.vin_gen = rand_gen;
    seq.start(env.agent.seqr);
    phase.drop_objection(this);
  endtask
endclass 
