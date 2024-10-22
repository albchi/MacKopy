module abs_memory_model
  #(parameter ASIZE=8,
    parameter DSIZE=8)
   (input              clk,
    input 	       we,
    input [ASIZE-1:0]  addr,
    input [DSIZE-1:0]  mem_in,
    output [DSIZE-1:0] mem_out,
    output [DSIZE-1:0] mem_res);
   
   logic [ASIZE-1:0] res_addr;
   logic [DSIZE-1:0] free_data;
   logic [DSIZE-1:0] mem_data;

   always @(posedge clk)
     if (we) begin
        res_addr <= addr;
        mem_data <= mem_in;
     end

   assign mem_out = (addr==res_addr)? mem_data : free_data;
   assign mem_res = mem_data;

endmodule // abs_memory_model
