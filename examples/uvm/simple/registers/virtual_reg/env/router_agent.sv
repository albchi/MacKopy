/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 ********************************************************************/

`ifndef ROUTER_AGENT__SV
`define ROUTER_AGENT__SV

`include "./packet_sequence.sv"
`include "./driver.sv"

// Lab 5 - Task 3, Step 2
// include the iMonitor.sv file
//
// ToDo
`include "./iMonitor.sv"


typedef uvm_sequencer #(packet) packet_sequencer;

class router_agent extends uvm_agent;
  packet_sequencer seqr;
  driver           drv;

  // Lab 5 - Task 3, Step 3
  // Add an instance of iMonitor.  Call it mon.
  //
  // ToDo
  iMonitor mon;


  `uvm_component_utils(router_agent)

  function new(string name, uvm_component parent);
    super.new(name, parent);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);

    // Lab 5 - Task 3, Step 4
    // Check the state of the is_active flag.
    //
    // If the is_active flag is UVM_ACTIVE, construct seqr, drv and mon
    // If the is_active flag is UVM_PASSIVE then only construct mon
    //
    // ToDo
    if (is_active) begin
      seqr = packet_sequencer::type_id::create("seqr", this);
      drv  = driver::type_id::create("drv", this);
    end
    mon = iMonitor::type_id::create("mon", this);


  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);

    // Lab 5 - Task 3, Step 5
    // Check the state of the is_active flag.
    //
    // If the is_active flag is UVM_ACTIVE, connect drv's seq_item_port to seqr's seq_item_export
    //
    // ToDo
    if (is_active) begin
      drv.seq_item_port.connect(seqr.seq_item_export);
    end


  endfunction

endclass

`endif
