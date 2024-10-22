module tb_alu
  (input logic        clk,
   input logic        rst_n,
   input logic        random_start,
   input logic [7:0]  random_opcode,
   input logic [19:0] random_addr);

   logic ready;
   logic start;
   assign start = random_start & ready;

   alu dut
     (.clk    (clk),
      .rst_n  (rst_n),
      .start  (random_start),
      .opcode (random_opcode),
      .addr   (random_addr),
      .ready  (ready)
      );

   localparam IDLE = 2'b00;
   localparam OP2  = 2'b01;
   localparam RES  = 2'b10;

   logic [1:0]  alu_state;
   logic [15:0] op1_data, op2_data;
   logic [15:0] res_data;
   logic [19:0] res_addr;

   always @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
         op1_data  <= 'b0;
         op2_data  <= 'b0;
         res_addr  <= 'b0;
         alu_state <= IDLE;
      end else begin
         case (alu_state)
           IDLE : begin
              if (start) begin
                 op1_data  <= dut.mem_out;
                 alu_state <= OP2;
              end
           end
           OP2 : begin
              op2_data  <= dut.mem_out;
              alu_state <= RES;
           end
           RES : begin
              res_addr  <= random_addr;
              alu_state <= IDLE;
           end
           default : begin
              alu_state <= IDLE;
           end
         endcase // case (alu_state)
      end
   end

// constraints for random_start
//asm_start_stable : assume property (@(posedge clk) disable iff (~rst_n)
//                                    (random_start && !ready) |=> random_start);

asm_start_interval : assume property (@(posedge clk) disable iff (~rst_n)
                                      (random_start && ready) |=> (!random_start)[*2]);

// constraints for random_opcode
//asm_opcode_stable : assume property (@(posedge clk) disable iff (~rst_n)
//                                     (random_start && !ready) |=> $stable(random_opcode));

asm_opcode_valid : assume property (@(posedge clk) disable iff (~rst_n)
                                     random_start |-> (random_opcode==8'h05 || random_opcode==8'h06));

// assertion to check add (opcode==8'h05)
ast_add_check: assert property (@(posedge clk) disable iff (~rst_n)
                                (start && random_opcode==8'h05)
                                |-> ##3 (res_data == (op1_data + op2_data)));

// assertion to check mul (opcode==8'h06)
//ast_mul_check: assert property (@(posedge clk) disable iff (~rst_n)
//                                (start && random_opcode==8'h06)
//                                |-> ##3 (res_data == (op1_data * op2_data)));

   abs_memory_model
     #(.ASIZE(20), .DSIZE(16))
   abs_mem
     (.clk      (clk),
      .we       (dut.we),
      .addr     (dut.addr),
      .mem_in   (dut.mem_in),
      .mem_out  (dut.mem_out),
      .mem_res  (res_data));

endmodule
