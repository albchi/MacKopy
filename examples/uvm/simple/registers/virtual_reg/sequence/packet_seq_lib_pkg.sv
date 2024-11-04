/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 ********************************************************************/

// Declare a package called packet_seq_lib_pkg.
package packet_seq_lib_pkg;

import uvm_pkg::*;

// The packet class is moved inside the package.
//
class packet extends uvm_sequence_item;
  rand bit[3:0] sa, da;
  rand bit[7:0] payload[$];

  `uvm_object_utils_begin(packet)
    `uvm_field_int(sa, UVM_ALL_ON + UVM_NOCOMPARE)
    `uvm_field_int(da, UVM_ALL_ON)
    `uvm_field_queue_int(payload, UVM_ALL_ON)
  `uvm_object_utils_end

  constraint valid {
    payload.size inside {[1:10]};
  }

  function new(string name="packet");
    super.new(name);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH)
  endfunction
endclass

//
// Every sequencen library that you create will have the identical structure.
// The only thing that changes is the name of the class and the sequence item type.
//
// The uvm_sequence_library_utils macro creates the infrastructure for the sequence
// library class.  The macro and the init_sequence_library() call are required to
// to be able to populate the sequence library with sequences are registered
// with it or any of its base classes.
//
class packet_seq_lib extends uvm_sequence_library #(packet);
  `uvm_object_utils(packet_seq_lib)
  `uvm_sequence_library_utils(packet_seq_lib)

  function new(string name = "packet_seq_lib");
    super.new(name);
    `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
    init_sequence_library();
  endfunction
endclass

endpackage
