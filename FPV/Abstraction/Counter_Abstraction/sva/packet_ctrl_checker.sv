module packet_ctrl_checker
  #(parameter PKT_WIDTH  = 8,
    parameter PKT_LENGTH = 4,
    parameter DATA_WIDTH = (PKT_WIDTH*PKT_LENGTH))
   (input logic clk,
    input logic rst,
    input logic [1:0] link_state,
    input logic link_rcv,
    input logic link_req,
    input logic link_ack,
    input logic link_down,
    input logic pkt_req,
    input logic pkt_ack,
    input logic [DATA_WIDTH-1:0] data,
    input logic [PKT_WIDTH-1:0]  pkt,
    input logic pkt_sop,
    input logic pkt_eop);

   localparam PLEN_WIDTH = $clog2(PKT_LENGTH);

   // check the relation between pkt_sop and pkt_eop - packet length
   //  pkt_sop is seen, pkt_eop should be seen after (PKT_LENGTH-1) cycles

   bit [PLEN_WIDTH:0] pktlength;

   always @(posedge clk or posedge rst) begin
      if (rst) begin
         pktlength <= 'd0;
      end else begin
         if (pkt_sop) begin
            pktlength <= 'd1;
         end else if (!pkt_eop && pktlength>='d1) begin
            pktlength <= pktlength + 'd1;
         end
      end
   end

   ast_pkt_length_check : assert property
      (@(posedge clk) disable iff (rst)
         pkt_eop |-> (pktlength == PKT_LENGTH));

   ast_link_state_init : assert property
      (@(posedge clk) disable iff (rst)
         $fell(rst) |-> (link_state == 2'b00));

   ast_link_state_init_to_busy : assert property
      (@(posedge clk) disable iff (rst)
         (link_state == 2'b00 ##1 link_state != 2'b00) |-> (link_state == 2'b01));

   ast_link_state_busy_to_ready : assert property
      (@(posedge clk) disable iff (rst)
         //(link_state == 2'b01) |=> (link_state inside {2'b01, 2'b10}));
         (link_state == 2'b01 ##1 link_state != 2'b01) |-> (link_state == 2'b10));

   ast_link_state_ready_to_up : assert property
      (@(posedge clk) disable iff (rst)
         //(link_state == 2'b10) |=> (link_state inside {2'b10, 2'b11}));
         (link_state == 2'b10 ##1 link_state != 2'b10) |-> (link_state == 2'b11));

endmodule

bind packet_ctrl packet_ctrl_checker #(.PKT_WIDTH(PKT_WIDTH), .PKT_LENGTH(PKT_LENGTH)) pkt_chkr (.*);

