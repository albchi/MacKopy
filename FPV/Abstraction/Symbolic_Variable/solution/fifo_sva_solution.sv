module fifo_sva  
  #(parameter WIDTH = 4,
    parameter DEPTH = 16,
    parameter L2D = 4
    )
   
   (input clk,
    input resetn,
    input [WIDTH-1:0] data_in,
    input push_req,
    input push_ack,
    input pop_req,
    input pop_ack,
    input [WIDTH-1:0] data_out,
    input full,
    input empty
    );

   // -- Macro for clocking condition of assertions
   // -- we could also use default clocking when only one clock
`define clk_rst @(posedge clk) disable iff (!resetn)
  

 // -- Hsk Signals
   wire   push_hsk;
   wire   pop_hsk;

   assign push_hsk = push_req && push_ack;
   assign pop_hsk  = pop_req && pop_ack;


   // --------------------------------------------------------------------------
   // -- FIFO Counter - Keep track of no. of outstanding entries
   // --------------------------------------------------------------------------

   reg [L2D:0] fullness_counter;
   wire [L2D:0] fullness_counter_nxt;

   assign 	fullness_counter_nxt = fullness_counter + push_hsk - pop_hsk;
   
    always @(posedge clk or negedge resetn)
     if (!resetn)
       fullness_counter <= {(L2D+1){1'b0}};
     else fullness_counter <= fullness_counter_nxt;


   // ---------------------------------------------------------------------------
   // -- Constraints
   // ---------------------------------------------------------------------------
  
  //Q1. Code constraints on push_req and pop_req to meet the requirements

  am_push_req_stable_when_no_ack:
     assume property (`clk_rst push_req && !push_ack
		      |=> $stable({push_req, data_in}));

   am_pop_hsk_req_stable_when_no_ack:
     assume property (`clk_rst pop_req && !pop_ack |=> pop_req);


   // ---------------------------------------------------------------------------
  


   // --------------------------------------------------------------------------
   // -- Assertions
   // --------------------------------------------------------------------------  

   //Q2. Code assertions to check design behavior 
   
   as_full_flag_correct:
     assert property (`clk_rst (fullness_counter == DEPTH) == full);

   as_empty_flag_correct:
     assert property (`clk_rst (fullness_counter == 0) == empty);

   as_no_push_ack_on_full:
     assert property (`clk_rst full |-> !push_ack);

   as_no_pop_ack_on_empty:
     assert property (`clk_rst empty |-> !pop_ack);

 // ---------------------------------------------------------------------------



   // --------------------------------------------------------------------------
   // -- Data Integrity Check Modelling - Formal Scoreboard
   // --------------------------------------------------------------------------

    
   // -- The symbolic data - this will be left floating
   logic [WIDTH-1:0] symb_data;

   // -- Event windows for seen in and seen out
   reg 	  symb_data_in;
   reg 	  symb_data_out;

   // -- Counter to keep track of how many items are ahead of the symb data
   reg [L2D:0] data_ahead_counter;
   wire [L2D:0] data_ahead_counter_nxt;
   wire 	incr;
   wire 	decr;
   
   
		       		      
   // The symbolic_data_in flag will be set when the symbolic data is seen at the
   //    input of the DUT AND it is pushed into the fifo successfully
   always @(posedge clk or negedge resetn)
     if (!resetn)
       symb_data_in <= 1'b0;
     else if (push_hsk && data_in == symb_data)
       symb_data_in <= 1'b1;
      

   // -- Symb data out gets set when our counter has reduced to one and we have 
   // -- a pop hsk    
   always @(posedge clk or negedge resetn)
     if (!resetn)
       symb_data_out <= 1'b0;
     else if (symb_data_in && (data_ahead_counter == 1) && pop_hsk)
       symb_data_out <= 1'b1;


   // -- Data ahead counter gets updated 
   always @(posedge clk or negedge resetn)
     if (!resetn)
       data_ahead_counter <= {L2D+1{1'b0}};
     else data_ahead_counter <= data_ahead_counter_nxt;
   

    // -- Increment the counter on any push hsk when we havent seen symb data in
   assign incr = push_hsk && !symb_data_in;

   // -- Decrement the counter on any pop hsk when we havent seen symb data out
   assign decr = pop_hsk && !symb_data_out;

   // -- Next state of the counter is current + incr - decr
   assign data_ahead_counter_nxt = data_ahead_counter + incr - decr;
   


   // ---------------------------------------------------------------------------
   // -- Constraints
   // ---------------------------------------------------------------------------


   // Q3. Code constraint to make the symbolic data stable
   // Once the symbolic data is in the model, it has to be kept stable
   //    and the tool should not change it again. 
   // Otherwise, the tool will not track one specific symbol but will be free
   //    to falsify our property using whatever data it chooses
   am_data_symb_stable:
     assume property (`clk_rst $stable(symb_data));

   // ---------------------------------------------------------------------------


   // --------------------------------------------------------------------------
   // -- Assertions
   // --------------------------------------------------------------------------    
  

   // Q4. Code data integrity check as discussed    
   // Assert that the data coming out of DUT is equal to our stored symbolic data
   // This can only be checked if certain preconditions are met. 
   // Figure out the antecedent first.
   as_data_integrity:
     assert property (`clk_rst  (symb_data_in && !symb_data_out &&
				 (data_ahead_counter == 1) && pop_hsk) 
				|=> 
				(data_out == symb_data) );
		      

 // ---------------------------------------------------------------------------




 endmodule
