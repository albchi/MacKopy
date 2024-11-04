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
// SV-AMS Custom Source Generators
//
//-----------------------------------------------------------------------------

`include "amp.sv"
`include "uvm_ams.sv"

////////////////////////////////////////////////////////////
class rc_voltage_gen extends sv_ams_generic_src;
  local real vdd;
  local real T;
  local real rc;

  function new(real v_min=0, real v_max=1.0, real f=1.0E6, real rc=1.0E-6);
    this.set_v_range(v_min,v_max);
    this.rc = rc * 1.0E9;
    this.set_frequency(f);
  endfunction
    
  virtual function real get_voltage();
    real r = vdd * exp(-this.get_time()/rc) + this.v_min.get_real();
    this.v.set_real(r);
    return r;
  endfunction

  virtual function void set_frequency(real f);
    this.T = (1.0E9 / f);
    this.vdd = this.v_max.get_real() - this.v_min.get_real();
  endfunction
endclass

////////////////////////////////////////////////////////////
module top;
  real out;
  logic sample=0;
  ams_src_if aif(sample);
  
  amp#(2.50) dut(aif.v, out);

  always #5 sample = ~sample;

  initial begin
    $vcdpluson;
    uvm_resource_db#(virtual ams_src_if)::set("*", "uvm_ams_src_if", aif, null);
    run_test();
  end
endmodule

////////////////////////////////////////////////////////////
class test extends uvm_test;
  `uvm_component_utils(test)
   
  rc_voltage_gen rc_gen; 

  function new (string name = "test",uvm_component parent);
    super.new(name, parent);
  endfunction 

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rc_gen   = new(0.0, +1.0, 1.0E6, 2.0E-7);
    rc_gen.set_time_precision(sv_ams_units::one_us);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    #1_000; 
    phase.drop_objection(this);
  endtask
endclass

