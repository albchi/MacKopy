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
// Description : Analog driver
//
//-----------------------------------------------------------------------------

`ifndef __ANA_DRIVER_SV
`define __ANA_DRIVER_SV

virtual class ana_driver_callbacks extends uvm_callback;
  static string type_name = "ana_driver_callbacks";

  function new(string name="ana_driver_callbacks");
    super.new(name);
  endfunction

  virtual function string get_type_name();
    return type_name;
  endfunction

  virtual task post_trans(sv_ams_real vin);
  endtask
endclass

class ana_driver extends uvm_driver#(sv_ams_real);

  virtual ana_comp_if ana_port;

  `uvm_component_utils(ana_driver)
  `uvm_register_cb(ana_driver, ana_driver_callbacks)

  function new(string name = "ana_driver", uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_resource_db#(virtual ana_comp_if)::read_by_name(get_full_name(), "ana_vif", ana_port))
      `uvm_error("TESTERROR", $sformatf("%s %s", "no bus interface ana_comp_if available at path=", get_full_name()));
  endfunction

  virtual task run_phase(uvm_phase phase);
    sv_ams_real vin_data;
    super.run_phase(phase);

    fork
      forever begin
        @(ana_port.mck);
        seq_item_port.get_next_item(vin_data);
        `uvm_info(get_type_name(), $psprintf("Driving In Voltage: %g", vin_data.get_real()),UVM_HIGH);
        ana_port.mck.vin  <= vin_data.get_real();
        `uvm_do_callbacks(ana_driver,ana_driver_callbacks, post_trans(vin_data));
        seq_item_port.item_done();
      end
    join_none
  endtask
endclass
`endif
