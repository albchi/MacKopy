program test();

import uvm_pkg::*;
import ubus_pkg::*;

`include "test_lib.sv"

`ifdef new_test 

// Large word read/write test
class test_r8_w8_r4_w4 extends ubus_example_base_test;

  `uvm_component_utils(test_r8_w8_r4_w4)

  function new(string name = "test_r8_w8_r4_w4", uvm_component parent=null);
    super.new(name,parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
  begin
    super.build_phase(phase);
    uvm_config_db#(uvm_object_wrapper)::set(this,
                      "ubus_example_tb0.ubus0.masters[0].sequencer.run_phase", 
                               "default_sequence",
                                r8_w8_r4_w4_seq::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this,
                      "ubus_example_tb0.ubus0.slaves[0].sequencer.run_phase", 
                               "default_sequence",
                                slave_memory_seq::type_id::get());
  end
  endfunction : build_phase

endclass : test_r8_w8_r4_w4 

`endif   


  initial begin
    uvm_config_db#(virtual ubus_if)::set(uvm_root::get(), "*", "vif", ubus_tb_top.vif);
    run_test();
  end

endprogram
