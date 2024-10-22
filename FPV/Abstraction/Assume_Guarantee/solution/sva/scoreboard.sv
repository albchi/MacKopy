//=======================================================================
// COPYRIGHT (C) 2015-2018 SYNOPSYS INC.
// This software and the associated documentation are confidential and
// proprietary to Synopsys, Inc. Your use or disclosure of this software
// is subject to the terms and conditions of a written license agreement
// between you, or your company, and Synopsys, Inc. In the event of
// publications, the following notice is applicable:
//
// ALL RIGHTS RESERVED
//
// The entire notice above must be reproduced on all authorized copies.
//-----------------------------------------------------------------------

module scoreboard
  #(parameter WIDTH = 32,
    parameter DEPTH =  8)
   (input logic             Resetn,
    input logic 	    Clk,
    input logic 	    ValidIn,
    input logic [WIDTH-1:0] DataIn,
    input logic 	    ValidOut,
    input logic [WIDTH-1:0] DataOut);

   localparam DPWIDTH = $clog2(DEPTH+1);

   logic [DPWIDTH-1:0] DpCnts;

   always @(posedge Clk or negedge Resetn)
     if (!Resetn) begin
	DpCnts <= 'd0;
     end else begin
	DpCnts <= DpCnts + ValidIn - ValidOut;
     end

   // ------------------------------------------------------
   // For latency check
   //   - generate CoverIn and CoverOut events
   //   - used to check latency
   // ------------------------------------------------------

   bit [WIDTH-1:0]   symb_data;
   bit 		     symb_iseen;
   bit 		     symb_oseen;
   bit 		     symb_idone;
   bit 		     symb_odone;
   bit [DPWIDTH-1:0] dcnts;

   assign symb_iseen = ValidIn  & (DataIn==symb_data) & ~symb_idone;
   assign symb_oseen = ValidOut & symb_idone & (dcnts=='d1) & ~symb_odone;

   always @(posedge Clk or negedge Resetn)
     if (!Resetn) begin
	symb_idone <= 1'b0;
     end else begin
	if (symb_iseen) symb_idone <= 1'b1;
     end
   always @(posedge Clk or negedge Resetn)
     if (!Resetn) begin
	symb_odone <= 1'b0;
     end else begin
	if (symb_oseen) symb_odone <= 1'b1;
     end

   always @(posedge Clk or negedge Resetn)
     if (!Resetn) begin
	dcnts <= 'd0;
     end else begin
	dcnts <= dcnts + (ValidIn & ~symb_idone) - (ValidOut & ~symb_odone);
     end

   // Constraints for symbolic data
   asm_symb_data_stable : assume property
      (@(posedge Clk) disable iff (!Resetn)
         symb_idone |-> $stable(symb_data));

   // Property definitions
   property p_data_integrity;
      @(posedge Clk) disable iff (!Resetn)
	symb_oseen |-> (DataOut==symb_data);
   endproperty
   property p_no_overflow;
      @(posedge Clk) disable iff (!Resetn)
	ValidIn |-> ((DpCnts<DEPTH) || ValidOut);
   endproperty
   property p_no_underflow;
      @(posedge Clk) disable iff (!Resetn)
	ValidOut |-> ((DpCnts>'d0) || ValidIn);
   endproperty

   // Assertions
   ast_data_integrity : assert property(p_data_integrity);
   //ast_no_overflow    : assert property(p_no_overflow);
   //ast_no_underflow   : assert property(p_no_underflow);

endmodule
