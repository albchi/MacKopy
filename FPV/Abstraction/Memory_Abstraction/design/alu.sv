
module alu (
   input logic clk,
   input logic rst_n,
   input logic start,
   input logic [7:0] opcode,
   input logic [19:0] addr,
   output logic ready
  );

  bit [2:0] state;
  bit [15:0] op1, op2;
  bit [7:0] code;

  wire [15:0] mem_out;
  wire [15:0] mem_in = (code==8'h05) ? op1 + op2 :
                       (code==8'h06) ? op1 * op2 :
                       16'b0;

  wire we = (state == 2'b10);
  assign ready = (state == 2'b00);

  always @(posedge clk or negedge rst_n) begin
     if (~rst_n) begin
        state <= 2'b0;
     end
     else begin
        case (state) 
          2'b00: begin
                  if (start) begin
                      op1 <= mem_out;
                      state <= 2'b01;
                      code <= opcode;
                  end
                end
          2'b01: begin
                  op2 <= mem_out;
                  state <= 2'b10;
                end
          2'b10: begin
                  state <= 2'b00;
                end
        endcase
     end
  end

  memblk #(20, 16) mem (
     .clk (clk),
     .we (we),
     .addr (addr),
     .mem_in (mem_in),
     .mem_out (mem_out)
  );

endmodule

module memblk #(ASIZE=8, DSIZE=8) (
   input clk,
   input we,
   input [ASIZE-1:0] addr,
   input [DSIZE-1:0] mem_in,
   output[DSIZE-1:0] mem_out
   );

   localparam NWORDS = 2**ASIZE;

   bit [15:0] core [NWORDS];

   assign mem_out = core[addr];

   always @(posedge clk) begin
      if (we) core[addr] <= mem_in;
   end

endmodule
