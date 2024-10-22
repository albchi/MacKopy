/*
   link_state
     2'b00 : Initial
     2'b01 : Busy - waiting stabled
     2'b10 : Ready - start req-ack handshake
     2'b11 : Up - ready to send packet
     transit from Initial -> Busy -> Ready -> Up
*/

module packet_ctrl
  #(parameter PKT_WIDTH  = 8,
    parameter PKT_LENGTH = 4,
    parameter DATA_WIDTH = (PKT_WIDTH*PKT_LENGTH))
   (input  logic clk,
    input  logic rst,
    output logic [1:0] link_state,
    input  logic link_rcv,
    output logic link_req,
    input  logic link_ack,
    input  logic link_down,
    input  logic pkt_req,
    output logic pkt_ack,
    input  logic [DATA_WIDTH-1:0] data,
    output logic [PKT_WIDTH-1:0]  pkt,
    output logic pkt_sop,
    output logic pkt_eop);

   localparam CNTS_WIDTH = 16;
   localparam BUSY_CNTS  = 600;
   localparam READY_CNTS = 65392;
   localparam PLEN_WIDTH = $clog2(PKT_LENGTH);

   typedef enum logic [1:0] {
      INIT=2'b00, BUSY=2'b01, WAITACK=2'b10, LINKUP=2'b11
   } link_state_e;

   typedef enum {
      IDLE, ACKED, SENDING, COMPLETE
   } pkt_state_e;

   link_state_e link_fsm;
   pkt_state_e  pkt_fsm;

   logic [CNTS_WIDTH-1:0] init_counts;
   logic                  clr_counts;
   logic                  incr_counts;
   logic [PLEN_WIDTH:0]   pkt_len;
   logic [DATA_WIDTH-1:0] sdata;

   assign link_state = link_fsm;

   always @(posedge clk or posedge rst) begin
      if (rst) begin
         link_req <= 1'b0;
         link_fsm <= INIT;
      end else begin
         case (link_fsm)
            INIT : begin
               if (init_counts == BUSY_CNTS) begin
                  link_fsm <= BUSY;
               end else
               if (init_counts == READY_CNTS) begin
                  link_req <= 1'b1;
                  link_fsm <= WAITACK;
               end
            end
            BUSY : begin
               if (init_counts == READY_CNTS) begin
                  link_req <= 1'b1;
                  link_fsm <= WAITACK;
               end
            end
            WAITACK : begin
               if (link_ack) begin
                  link_req <= 1'b0;
                  link_fsm <= LINKUP;
               end
            end
            LINKUP : begin
               if (link_down) begin
                  link_fsm <= INIT;
               end
            end
         endcase
      end
   end

   assign clr_counts  = (link_fsm == LINKUP);
   //assign incr_counts = (link_fsm inside {INIT, BUSY}) & link_rcv;
   assign incr_counts = (link_fsm != LINKUP) & link_rcv;

   always @(posedge clk or posedge rst) begin
      if (rst) begin
         init_counts <= 'b0;
      end else begin
         if (clr_counts) begin
            init_counts <= 'b0;
         end else
         if (incr_counts) begin
            init_counts <= init_counts + 'd1;
         end
      end
   end

   always @(posedge clk or posedge rst) begin
      if (rst) begin
         pkt_ack <= 1'b0;
         pkt_sop <= 1'b0;
         pkt_eop <= 1'b0;
         pkt     <=  'b0;
         pkt_len <=  'b0;
         sdata   <=  'b0;
         pkt_fsm <= IDLE;
      end else begin
         case (pkt_fsm)
            IDLE : begin
               if (link_fsm == LINKUP && pkt_req) begin
                  pkt_ack <= 1'b1;
                  sdata   <= data;
                  pkt_fsm <= ACKED;
               end
            end
            ACKED : begin
               pkt_sop <= 1'b1;
               pkt_len <=  'd1;
               pkt     <= sdata[PKT_WIDTH-1:0];
               sdata   <= sdata >> PKT_WIDTH;
               pkt_fsm <= SENDING;
            end
            SENDING : begin
               pkt_sop <= 1'b0;
               pkt_len <= pkt_len + 'd1;
               pkt     <= sdata[PKT_WIDTH-1:0];
               sdata   <= sdata >> PKT_WIDTH;
               if (pkt_len == PKT_LENGTH) begin
                  pkt_eop <= 1'b1;
                  pkt_fsm <= COMPLETE;
               end
            end
            COMPLETE : begin
               pkt_eop <= 1'b0;
               pkt_len <=  'd0;
               pkt_fsm <= IDLE;
            end
         endcase
      end
   end

endmodule

