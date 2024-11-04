`ifndef INTERFACE_SVH_
`define INTERFACE_SVH_

//File contains all interface definitions
//Input utopia interface
interface atm_interface;
  logic clk;
  logic [7:0] data;
  logic soc;
  logic en;
  logic empty_full;
  modport tx (output clk, data, soc, en,
              input empty_full );
  modport rx (output clk, en,
              input  data, soc, empty_full );
endinterface

`endif
