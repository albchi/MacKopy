/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 ********************************************************************/


`ifndef PACKET_SEQUENCE__SV
`define PACKET_SEQUENCE__SV

// Lab 6 - Task 3, Step 2
// The packet class now resides inside the packet sequence library package.
//
// Replace the following include statement with an import of the packet sequence library package:
// import packet_seq_lib_pkg::*;
//
// ToDo
import packet_seq_lib_pkg::*;


class packet_sequence extends uvm_sequence #(packet);

  // Lab 6 - Task 3, Step 3
  // Register the sequence in the packet sequence library:
  //
  // `uvm_add_to_seq_lib(packet_sequence, packet_seq_lib)
  //
  // ToDo
  `uvm_add_to_seq_lib(packet_sequence, packet_seq_lib)

  int       item_count = 10;
  bit[15:0] sa_enable  = '1;
  bit[15:0] da_enable  = '1;
  int       valid_sa[$];
  int       valid_da[$];

  `uvm_object_utils_begin(packet_sequence)
    `uvm_field_int(item_count, UVM_ALL_ON)
    `uvm_field_int(sa_enable, UVM_ALL_ON)
    `uvm_field_int(da_enable, UVM_ALL_ON)
    `uvm_field_queue_int(valid_sa, UVM_ALL_ON)
    `uvm_field_queue_int(valid_da, UVM_ALL_ON)
  `uvm_object_utils_end

  function void pre_randomize();
    int number_of_addresses;
    uvm_config_db#(bit[15:0])::get(m_sequencer, "*", "sa_enable", sa_enable);
    uvm_config_db#(bit[15:0])::get(m_sequencer, "*", "da_enable", da_enable);

    number_of_addresses = $size(sa_enable, 1);
    valid_sa.delete();
    for (int i=0; i<number_of_addresses; i++)
      if (sa_enable[i])
        valid_sa.push_back(i);
    number_of_addresses = $size(da_enable, 1);
    valid_da.delete();
    for (int i=0; i<number_of_addresses; i++)
      if (da_enable[i])
        valid_da.push_back(i);
  endfunction

  function new(string name = "packet_sequence");
    super.new(name);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
  endfunction

  virtual task body();

    // Lab 6 - Task 3, Step 4
    // Create a parent sequence handle, call it parent.
    // 
    // uvm_sequence_base parent;
    //
    // ToDo
    uvm_sequence_base parent;

    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
    uvm_config_db#(int)::get(m_sequencer, "*", "item_count", item_count);

    // Lab 6 - Task 3, Step 5 and 6
    // Call get_parent_sequence() to retrive the parent sequence handle.
    //
    // If parent handle is not null, set the sequence's start_phase to parent
    // sequence's starting_phase.
    //
    // This is necessary, because child sequences do not have start_phase of their own.
    // 
    // parent = get_parent_sequence();
    // if (parent != null) begin
    //   starting_phase = parent.starting_phase;
    // end
    //
    // ToDo
    parent = get_parent_sequence();
    if (parent != null) begin
      starting_phase = parent.starting_phase;
    end

    if (starting_phase != null) begin
      uvm_objection objection = starting_phase.get_objection();
      objection.set_drain_time(this, 1us);
      starting_phase.raise_objection(this);
    end

    repeat(item_count) begin
      `uvm_do_with(req, {sa inside valid_sa; da inside valid_da;});
    end

    if (starting_phase != null) begin
      starting_phase.drop_objection(this);
    end
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
class packet_noop_sequence extends uvm_sequence #(packet);
  `uvm_object_utils(packet_noop_sequence)
  function new(string name = "packet_noop_sequence");
    super.new(name);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
  endfunction

  virtual task body();
  endtask
endclass

`endif
