//-------------------------------------------------------------
//    Copyright 2011 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary work of
// Synopsys, Inc., and is fully protected under copyright and trade
// secret laws. You may not view, use, disclose, copy, or distribute this
// file or any information contained herein except pursuant to a valid
// written license from Synopsys.
//
//-------------------------------------------------------------


`include "ral_sys.sv"
`include "vcs/snps_reg.svh"

program test;

import "DPI-C" function int comp1_drv(int ctxt);
   
initial
begin
   ral_sys_sys sys = new("Sys");
   uvm_reg::include_coverage("*", UVM_NO_COVERAGE);
   sys.build();
   comp1_drv(snps_reg::create_context(sys.Comp1a));
   comp1_drv(snps_reg::create_context(sys.Comp1b, sys.default_map));
end

endprogram

