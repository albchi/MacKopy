/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   * 
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 ********************************************************************/

`ifndef RESET_SEQUENCE__SV
`define RESET_SEQUENCE__SV

class reset_sequence extends uvm_sequence;

  // Lab 4 - Task 6, Step 2
  //
  // Create an instance of the DUT virtual interface (router_io), call it sigs.
  //
  // ToDo
  virtual router_io sigs;

  `uvm_object_utils(reset_sequence)

  function new(string name = "reset_sequence");
    super.new(name);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
  endfunction

  task body();
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);

    // Lab 4 - Task 6, Step 3
    //
    // Use uvm_config_db(virtual router_io)::get() method to retrieve the DUT virtual interface
    //
    // ToDo
    if (!uvm_config_db#(virtual router_io)::get(m_sequencer, "*", "router_io", sigs)) begin
       `uvm_fatal("CFGERR", "Interface for Reset Sequence not set");
    end



    if (starting_phase != null)
      starting_phase.raise_objection(this);

    // Lab 4 - Task 6, Step 4
    //
    // Replace the following reset() call with reset_dut();
    //
    // ToDo
    reset_dut();

    if (starting_phase != null)
      starting_phase.drop_objection(this);
   endtask

  task reset();
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
    `uvm_info("RESET", "Executing Reset", UVM_MEDIUM);
  endtask

  //
  // In the interest of lab time, the following reset device driver has been done for you.
  //

  task reset_dut();
    sigs.reset_n = 1'b0;
    sigs.drvClk.frame_n <= '1;
    sigs.drvClk.valid_n <= '1;
    sigs.drvClk.din <= '1;
    ##2 sigs.drvClk.reset_n <= '1;
    repeat(15) @(sigs.drvClk);
  endtask

endclass


//
// The following no operation (noop) sequence is created for the purpose of disabling the packet_sequencer
// by setting the sequencer's "default_sequence" field to this noop sequence.  This is necessary because
// in UVM 1.0, there is no way to disable the sequencer once the default_sequence is set to some sequence.
// Attempts to set "default_sequence" to "" to disable the sequencer does not work.  Nor trying to set
// "default_sequence" to null.
//
// So, for the moment, you are stuck with this work-around.
//
class reset_noop_sequence extends uvm_sequence #(packet);
  `uvm_object_utils(reset_noop_sequence)
  function new(string name = "reset_noop_sequence");
    super.new(name);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
  endfunction

  virtual task body();
  endtask
endclass

`endif
