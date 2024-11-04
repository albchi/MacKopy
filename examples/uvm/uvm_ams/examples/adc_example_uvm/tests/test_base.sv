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
// Description : Includes all tests
//
//-----------------------------------------------------------------------------

`include "ana_cfg.sv"
`include "ana_env.sv"

class ana_base_sequence extends uvm_sequence#(sv_ams_real);

  `uvm_object_utils(ana_base_sequence)
  sv_ams_generic_src  vin_gen;

  function new(string name = "ana_base_sequence");
    super.new(name);
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

  virtual task body();
    `uvm_create(req);
    vin_gen.get_voltage;
    req = vin_gen.v;
    `uvm_send(req);
  endtask

endclass


class ana_base_test extends uvm_test;
  `uvm_component_utils(ana_base_test)

  ana_env env;
  ana_cfg cfg;

  function new(string name = "base_test", uvm_component parent =  null);
    super.new(name, parent);
    cfg = ana_cfg::type_id::create("cfg");
    uvm_resource_db#(ana_cfg)::set("*","ana_cfg", cfg);
  endfunction

 function void build_phase(uvm_phase phase);
   env = ana_env::type_id::create("env",this);
 endfunction
endclass 
