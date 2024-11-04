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
// Description : Shows how to model reference model in SV using interface of reals
//
//-----------------------------------------------------------------------------

`ifndef __ANA_CHECKER_SV
`define __ANA_CHECKER_SV

class ana_checker extends uvm_component;
  virtual ana_comp_if ana_port;
  ana_cfg cfg;

  `uvm_component_utils_begin(ana_checker)
    `uvm_field_object(cfg, UVM_DEFAULT)
  `uvm_component_utils_end
   

  function new(string name = "ana_checker", uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_resource_db#(virtual ana_comp_if)::read_by_name(get_full_name(), "ana_vif", ana_port)) begin
	`uvm_error("TESTERROR", $sformatf("%s %s", "no bus interface ana_vif available at path=", get_full_name()));
    end
  
    if(!uvm_resource_db#(ana_cfg)::read_by_name(get_full_name(), "ana_cfg", cfg)) begin
	`uvm_error("TESTERROR", $sformatf("%s %s", "no valid configuratiuon available at path=", get_full_name()));
    end
    this.cfg = cfg;
  endfunction

  virtual task run();
    real vin;
    bit[3:0] o, exp_o;
    real exp_r;
    real vmid;
    int cnt=0;

    fork
    begin
      vmid = (cfg.max_voltage.get_real()-cfg.min_voltage.get_real())/2;
      forever begin
        @(ana_port.sck);
        if(cnt>0) begin
          vin =  ana_port.sck.vin;
          o[0] =  (ana_port.sck.o1 >= vmid) ? 1'b1 : 1'b0;
          o[1] =  (ana_port.sck.o2 >= vmid) ? 1'b1 : 1'b0;
          o[2] =  (ana_port.sck.o3 >= vmid) ? 1'b1 : 1'b0;
          o[3] =  (ana_port.sck.o4 >= vmid) ? 1'b1 : 1'b0;
       
          `uvm_info("NOTE", $psprintf("vin=%g, ADC Out=%04x", vin, o),UVM_MEDIUM);
          exp_r = vin * 16.0 / cfg.max_voltage.get_real();
          exp_o = floor(exp_r);
          if ((o!=exp_o) && (o!=exp_o+1)) 
            `uvm_warning("TESTWARNING",$psprintf("Mismatching output=%04x, expecting=%04x - %0.3f", o, exp_o, exp_r));
        end
        cnt++;
      end
    end
    join_none
  endtask

endclass
`endif
