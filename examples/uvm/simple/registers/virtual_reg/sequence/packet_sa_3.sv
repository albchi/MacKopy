/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   * 
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 ********************************************************************/

`ifndef PACKET_SA_3__SV
`define PACKET_SA_3__SV

class packet_sa_3 extends packet;
  `uvm_object_utils(packet_sa_3)

  // Lab 2 - set the constraint for source address (sa) to 3
  constraint sa_3 {
    sa == 3;
  }

  function new(string name = "packet_sa_3");
    super.new(name);
   `uvm_info("TRACE", $sformatf("%m"), UVM_HIGH);
  endfunction
endclass

`endif

