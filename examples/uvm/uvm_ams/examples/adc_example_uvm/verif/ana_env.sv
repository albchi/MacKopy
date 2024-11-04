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
// Description : Environment where all components are instantiated
//
//-----------------------------------------------------------------------------

`include "ana_agent.sv"
`include "ana_cov.sv"
`include "ana_driver2cov.sv"

typedef uvm_callbacks #(ana_driver,ana_driver_callbacks) ana_driver_cbs_t;

`ifndef __ANA_ENV_SV
`define __ANA_ENV_SV

class ana_env extends uvm_env;

  `uvm_component_utils(ana_env)

  ana_cfg     cfg;
  ana_agent   agent;
  ana_cov     cov;

  function new( string name = "ana_env", uvm_component parent = null);
     super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_resource_db#(ana_cfg)::read_by_name(get_full_name(), "ana_cfg", cfg)) 
      `uvm_error("TESTERROR", $sformatf("%s %s", "no valid configuratiuon available at path=", get_full_name()));

    this.cfg = cfg;
    agent = ana_agent::type_id::create("agent", this);
    cov =  ana_cov::type_id::create("cov", this);
  endfunction


  function void connect_phase(uvm_phase phase);
    ana_driver2cov  cov_cb;
    super.connect_phase(phase);

    cov_cb = new(cov);
    ana_driver_cbs_t::add(agent.drv,cov_cb);
  endfunction : connect_phase

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info(get_full_name, cfg.psdisplay(""),UVM_HIGH);
    fork
      forever begin
        @(tb.ana_if.clk);
        tb.ana_if.s = (tb.ana_if.clk) ? cfg.max_voltage.get_real() : cfg.min_voltage.get_real();
      end
    join_none
  endtask

endclass
`endif
