/* model counter with 2 special values
    INITIAL : counts == 0
    STAGE_1 : counts between 1 and SPV1
    SPVAL_1 : counts == SPV1
    STAGE_2 : counts between SPV1+1 and SPV2
    SPVAL_2 : counts == SPV2
    STAGE_3 : counts between SPV2+1 and maximum-1
    MAXCNTS : counts == maximum (all 1s)
 */

module abstracted_counter
  #(BIT_WIDTH = 8,
    SPVALUE_1 = 200,
    SPVALUE_2 = 249,
    DIRECTIVE = 0) // 0: use as assumes 1: use as asserts
   (input logic clk,
    input logic rst,
    input logic clr,
    input logic incr,
    input logic [BIT_WIDTH-1:0] counts);

   typedef enum bit [2:0] {
      INITIAL=3'd0, STAGE_1=3'd1, SPVAL_1=3'd2, STAGE_2=3'd3, 
      SPVAL_2=3'd4, STAGE_3=3'd5, MAXCNTS=3'd6, RESEVED=3'd7
   } counter_state_e;

   counter_state_e cur_state;

/* not used
   property p_state_not_reserved;
      @(posedge clk) disable iff (rst)
         (cur_state != RESERVED);
   endproperty
 */
// -------------------------------------
// Properies for state transition
// -------------------------------------
   property p_initial_state;
      @(posedge clk) disable iff (rst)
         $fell(rst) |-> (cur_state == INITIAL);
   endproperty

   property p_next_state_clr;
      @(posedge clk) disable iff (rst)
         clr |=> (cur_state == INITIAL);
   endproperty

   property p_next_state_no_clr_incr;
      @(posedge clk) disable iff (rst)
         (!clr && !incr) |=> $stable(cur_state);
   endproperty

   property p_next_state_initial_incr;
      @(posedge clk) disable iff (rst)
         (cur_state == INITIAL && incr) |=> (cur_state == STAGE_1);
   endproperty

   property p_next_state_stage_1_incr;
      @(posedge clk) disable iff (rst)
         (cur_state == STAGE_1 && incr) |=> (cur_state inside {STAGE_1, SPVAL_1});
   endproperty

   property p_next_state_spval_1_incr;
      @(posedge clk) disable iff (rst)
         (cur_state == SPVAL_1 && incr) |=> (cur_state == STAGE_2);
   endproperty

   property p_next_state_stage_2_incr;
      @(posedge clk) disable iff (rst)
         (cur_state == STAGE_2 && incr) |=> (cur_state inside {STAGE_2, SPVAL_2});
   endproperty

   property p_next_state_spval_2_incr;
      @(posedge clk) disable iff (rst)
         (cur_state == SPVAL_2 && incr) |=> (cur_state == STAGE_3);
   endproperty

   property p_next_state_stage_3_incr;
      @(posedge clk) disable iff (rst)
         (cur_state == STAGE_3 && incr) |=> (cur_state inside {STAGE_3, MAXCNTS});
   endproperty

   property p_next_state_maxcnts_incr;
      @(posedge clk) disable iff (rst)
         (cur_state == MAXCNTS && incr) |=> (cur_state == INITIAL);
   endproperty

// -------------------------------------
// Properies for counter value per state
// -------------------------------------
   property p_counts_initial;
      @(posedge clk) disable iff (rst)
         (cur_state == INITIAL) |-> (counts == 'd0);
   endproperty

   property p_counts_stage_1;
      @(posedge clk) disable iff (rst)
         (cur_state == STAGE_1) |-> (counts > 'd0 && counts < SPVALUE_1);
   endproperty

   property p_counts_spval_1;
      @(posedge clk) disable iff (rst)
         (cur_state == SPVAL_1) |-> (counts == SPVALUE_1);
   endproperty

   property p_counts_stage_2;
      @(posedge clk) disable iff (rst)
         (cur_state == STAGE_2) |-> (counts > SPVALUE_1 && counts < SPVALUE_2);
   endproperty

   property p_counts_spval_2;
      @(posedge clk) disable iff (rst)
         (cur_state == SPVAL_2) |-> (counts == SPVALUE_2);
   endproperty

   property p_counts_stage_3;
      @(posedge clk) disable iff (rst)
         (cur_state == STAGE_3) |-> (counts > SPVALUE_2 && counts < {BIT_WIDTH{1'b1}});
   endproperty

   property p_counts_maxcnts;
      @(posedge clk) disable iff (rst)
         (cur_state == MAXCNTS) |-> (counts == {BIT_WIDTH{1'b1}});
   endproperty

// -------------------------------------------
// Properies for validation of abstraction
//   determine proper state per counter value
// -------------------------------------------
   property p_counts_initial_state;
      @(posedge clk) disable iff (rst)
         (counts == 'd0) |-> (cur_state == INITIAL);
   endproperty

   property p_counts_stage_1_state;
      @(posedge clk) disable iff (rst)
         (counts > 'd0 && counts < SPVALUE_1) |-> (cur_state == STAGE_1);
   endproperty

   property p_counts_spval_1_state;
      @(posedge clk) disable iff (rst)
         (counts == SPVALUE_1) |-> (cur_state == SPVAL_1);
   endproperty

   property p_counts_stage_2_state;
      @(posedge clk) disable iff (rst)
         (counts > SPVALUE_1 && counts < SPVALUE_2) |-> (cur_state == STAGE_2);
   endproperty

   property p_counts_spval_2_state;
      @(posedge clk) disable iff (rst)
         (counts == SPVALUE_2) |-> (cur_state == SPVAL_2);
   endproperty

   property p_counts_stage_3_state;
      @(posedge clk) disable iff (rst)
         (counts > SPVALUE_2 && counts < {BIT_WIDTH{1'b1}}) |-> (cur_state == STAGE_3);
   endproperty

   property p_counts_maxcnts_state;
      @(posedge clk) disable iff (rst)
         (counts == {BIT_WIDTH{1'b1}}) |-> (cur_state == MAXCNTS);
   endproperty

generate
   if (DIRECTIVE == 0) begin : ASM
      // use as counter abstraction
      asm_initial_state           : assume property(p_initial_state);
      asm_next_state_clr          : assume property(p_next_state_clr);
      asm_next_state_no_clr_incr  : assume property(p_next_state_no_clr_incr);
      asm_next_state_initial_incr : assume property(p_next_state_initial_incr);
      asm_next_state_stage_1_incr : assume property(p_next_state_stage_1_incr);
      asm_next_state_spval_1_incr : assume property(p_next_state_spval_1_incr);
      asm_next_state_stage_2_incr : assume property(p_next_state_stage_2_incr);
      asm_next_state_spval_2_incr : assume property(p_next_state_spval_2_incr);
      asm_next_state_stage_3_incr : assume property(p_next_state_stage_3_incr);
      asm_next_state_maxcnts_incr : assume property(p_next_state_maxcnts_incr);
      asm_counts_initial          : assume property(p_counts_initial);
      asm_counts_stage_1          : assume property(p_counts_stage_1);
      asm_counts_spval_1          : assume property(p_counts_spval_1);
      asm_counts_stage_2          : assume property(p_counts_stage_2);
      asm_counts_spval_2          : assume property(p_counts_spval_2);
      asm_counts_stage_3          : assume property(p_counts_stage_3);
      asm_counts_maxcnts          : assume property(p_counts_maxcnts);
   end : ASM
   else begin : AST
      // validate if counter abstraction is appropriate
      ast_initial_state           : assert property(p_initial_state);
      ast_next_state_clr          : assert property(p_next_state_clr);
      ast_next_state_no_clr_incr  : assert property(p_next_state_no_clr_incr);
      ast_next_state_initial_incr : assert property(p_next_state_initial_incr);
      ast_next_state_stage_1_incr : assert property(p_next_state_stage_1_incr);
      ast_next_state_spval_1_incr : assert property(p_next_state_spval_1_incr);
      ast_next_state_stage_2_incr : assert property(p_next_state_stage_2_incr);
      ast_next_state_spval_2_incr : assert property(p_next_state_spval_2_incr);
      ast_next_state_stage_3_incr : assert property(p_next_state_stage_3_incr);
      ast_next_state_maxcnts_incr : assert property(p_next_state_maxcnts_incr);
      ast_counts_initial          : assert property(p_counts_initial);
      ast_counts_stage_1          : assert property(p_counts_stage_1);
      ast_counts_spval_1          : assert property(p_counts_spval_1);
      ast_counts_stage_2          : assert property(p_counts_stage_2);
      ast_counts_spval_2          : assert property(p_counts_spval_2);
      ast_counts_stage_3          : assert property(p_counts_stage_3);
      ast_counts_maxcnts          : assert property(p_counts_maxcnts);
      asm_counts_initial_state    : assume property(p_counts_initial_state);
      asm_counts_stage_1_state    : assume property(p_counts_stage_1_state);
      asm_counts_spval_1_state    : assume property(p_counts_spval_1_state);
      asm_counts_stage_2_state    : assume property(p_counts_stage_2_state);
      asm_counts_spval_2_state    : assume property(p_counts_spval_2_state);
      asm_counts_stage_3_state    : assume property(p_counts_stage_3_state);
      asm_counts_maxcnts_state    : assume property(p_counts_maxcnts_state);
   end : AST
endgenerate

endmodule

