/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

////////////////////////////////////////////////////////////////////////////////
//  		
//		        	Traffic Light Controller
//   
//      INPUT : X ( Traffic pattern from testbench )
//      OUTPUT : hwy, cntry ( Light signals from this design )
//      Controlling parameter : ctl ( Internal register updated by CPU program )
//
//      controller.asm : Assembly programming 
//      --------------------------------------
//      It reads output state values of light signals, add delay and update the 
//      ctl register.
//
//
//      Address  Direction   Description
//        7E       R/W         Control:
//                                0  -  Enable.  Must set to '1' to get output.
//
//
////////////////////////////////////////////////////////////////////////////////


`define TRUE 1'b1
`define FALSE 1'b0
`define RED 2'd0
`define YELLOW 2'd1
`define GREEN 2'd2

//STATE DEFINATION          HWY     CNTRY
`define S0 3'd0         // GREEN     RED
`define S1 3'd1         // YELLOW    RED
`define S2 3'd2         // RED       RED
`define S3 3'd3         // RED       GREEN
`define S4 3'd4         // RED       YELLOW

module exp (
   		clk,
   		reset,

   		hwy,
   		cntry,

   		expdin,
   		expdout,
   		expaddr,
   		expread,
   		expwrite,
  		X
	   );

input clk;
input reset;
input X;

output [1:0] hwy;
output [1:0] cntry;

// Expansion Interface
output [7:0]	expdin;		// TO rics8 core
input [7:0]	expdout;	// FROM risc8 core
input [6:0]	expaddr;	// Address
input		expread;	// Asserted (high) when risc8 is reading
input		expwrite;	// Asserted (high) when risc8 is writing

// Outputs used as registers
reg [7:0] expdin;

reg [1:0] hwy;
reg [1:0] cntry;

// Programmable registers
reg [2:0]	ctl;
reg [2:0]       statedev;

reg [2:0] state;
reg [2:0] next_state;

always @(expread or expaddr) begin
   if (expread) begin
      case (expaddr)
         7'h7D:    expdin[7:0] <= statedev[2:0];
         default:  expdin[7:0] <= 0;
      endcase
   end
   else begin
	expdin <= expdin;
   end
end

always @(posedge clk) begin
   if (reset) begin
      ctl[2:0]      <= 0;
   end
   else begin
      if (expwrite) begin
         case (expaddr) // synopsys parallel_case
            7'h7E: ctl[2:0] <= expdout[7:0];
         endcase
      end
   end
end


//Signal controller state in S0 state
initial
begin
   state = `S0;
   next_state = `S0;
   hwy = `GREEN;
   cntry = `RED;
   expdin = 8'b00000000;
end

always @(ctl)
   state = next_state;

//Compute values of main signal and country signal
always @(state)
begin
 case(state)
   `S0: begin
          hwy =   `GREEN;
          cntry = `RED;
        end
  `S1: begin
          hwy = `YELLOW;
          cntry = `RED;
       end
  `S2: begin
          hwy = `RED;
          cntry = `RED;
       end
  `S3: begin
          hwy = `RED;
          cntry = `GREEN;
       end
  `S4: begin
          hwy = `RED;
          cntry = `YELLOW;
       end
  endcase
end

//State machine using case statements

always @(state or reset or X)
begin
 if(reset)
    begin
    next_state = `S0;
    statedev = 3'd0;
    end
 else
  case(state)
    `S0: if(X)
           begin
              next_state = `S1;
              statedev = 3'd1;
           end
         else
           begin
              next_state = `S0;
              statedev = 3'd0;
           end
   `S1: begin                
           next_state = `S2;
           statedev = 3'd2;
       end
  `S2: begin                 
          next_state = `S3;
          statedev = 3'd3;
       end
 `S3: if(X)
        begin
           next_state = `S3;
           statedev = 3'd3;
        end
      else
        begin
           next_state = `S4;
           statedev = 3'd4;
        end
 `S4: begin                   
         next_state = `S0;
         statedev = 3'd0;
      end
 default: 
     begin
        next_state = `S0;
        statedev = 3'd0;
     end
 endcase
end

endmodule
