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
// Description : Agent where all core components are instantiated
//
//-----------------------------------------------------------------------------

`ifndef __ANA_AGENT_SV
`define __ANA_AGENT_SV

`include "ana_driver.sv"
`include "ana_checker.sv"

class ana_agent extends uvm_agent;

  `uvm_component_utils(ana_agent)

  typedef uvm_sequencer#(sv_ams_real) ana_seqr;
  ana_cfg cfg;
  ana_driver  drv;
  ana_seqr    seqr;
  ana_checker chkr;

  function new( string name = "ana_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction
 
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_resource_db#(ana_cfg)::read_by_name(get_full_name(), "ana_cfg", cfg)) 
      `uvm_error("TESTERROR", $sformatf("%s %s", "no valid configuratiuon available at path=", get_full_name()));

    this.cfg = cfg;
    seqr = ana_seqr::type_id::create("seqr", this);
    drv = ana_driver::type_id::create("drv", this);
    chkr = ana_checker::type_id::create("chkr", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    drv.seq_item_port.connect(seqr.seq_item_export);
  endfunction : connect_phase
endclass
`endif

