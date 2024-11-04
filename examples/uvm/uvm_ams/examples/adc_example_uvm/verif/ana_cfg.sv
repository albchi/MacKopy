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
// Description : Testbench configuration. 
//
//-----------------------------------------------------------------------------

`ifndef __ANA_CFG_SV
`define __ANA_CFG_SV

class ana_cfg extends uvm_object;
  real MinVoltage = 0;
  real MaxVoltage = 1.800;
  real Frequency  = 2000; 
  real Accuracy   = `SV_AMS_REAL_DEF_ACCURACY;

  int      num_trans = 50;

  sv_ams_real min_voltage;
  sv_ams_real max_voltage;
  sv_ams_real accuracy;
  sv_ams_real frequency;

  `uvm_object_utils_begin(ana_cfg)
    `uvm_field_int(num_trans,UVM_ALL_ON)
    `uvm_field_real(MinVoltage,UVM_ALL_ON)
    `uvm_field_real(MaxVoltage,UVM_ALL_ON)
    `uvm_field_real(Frequency,UVM_ALL_ON)
    `uvm_field_real(Accuracy,UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "ana_cfg");
    super.new(name);
    min_voltage = new(MinVoltage);
    max_voltage = new(MaxVoltage);
    frequency   = new(Frequency*1E3, 1.0);
    accuracy    = new(Accuracy, 1.0);
  endfunction

  function string psdisplay(string prefix = "");
    psdisplay = $psprintf("%s Min Voltage=%0f, Max Voltage=%0f, Accuracy=%0d, Freq=%0d MHz NumTrans=%0d", 
                          prefix, min_voltage.get_real(), max_voltage.get_real(), 
                          accuracy.get_int(), frequency.get_real()/1e3, num_trans);
  endfunction
endclass
`endif
