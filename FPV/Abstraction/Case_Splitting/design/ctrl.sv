module ctrl
  #(parameter DATA_WIDTH = 64,
    parameter ADDR_WIDTH = 20,
    parameter LEN_WIDTH  =  3,
    parameter BEN_WIDTH  = (DATA_WIDTH/8))
   (input logic                   CLK,
    input logic                   RESETn,
    input logic [ADDR_WIDTH-1:0]  REQ_ADDR,
    input logic [LEN_WIDTH-1:0]   REQ_LEN,
    input logic [1:0]             REQ_SIZE,
    input logic                   REQ_VLD,
    output logic                  REQ_RDY,
    output logic                  RSP_LAST,
    output logic                  RSP_VLD,
    input logic                   RSP_RDY,
    output logic [BEN_WIDTH-1:0]  RSP_BEN,
    output logic [DATA_WIDTH-1:0] RSP_DATA,
    output logic                  DEV_REQ,
    input logic                   DEV_ACK,
    input logic [DATA_WIDTH-1:0]  DEV_DATA);

   localparam DEPTH = (1 << LEN_WIDTH);

   logic [DATA_WIDTH-1:0]         buffer [0:DEPTH-1];
   logic [DEPTH-1:0]              buff_vld;
   logic [LEN_WIDTH-1:0]          buff_len;
   logic [LEN_WIDTH:0]            wr_ptr;
   logic [LEN_WIDTH:0]            rd_ptr;
   logic                          wr_last;
   logic                          rd_last;
   logic [2:0]                    cur_addr;
   logic [1:0]                    cur_size;

   typedef enum {
      IDLE, DEV_RQST, WAIT_ACK, RTRN_RSP, WAIT_RDY
   } ctrl_state_e;

   ctrl_state_e state;

   // Expected ByteEnable
   //   REQ_SIZE = 2'b00 : Byte
   //     REQ_ADDR[2:0] = 3'b000 :
   //       1st beat: RSP_BEN=8'b00000001
   //       2nd beat: RSP_BEN=8'b00000010
   //       3rd beat: RSP_BEN=8'b00000100
   //       4th beat: RSP_BEN=8'b00001000
   //       5th beat: RSP_BEN=8'b00010000
   //       6th beat: RSP_BEN=8'b00100000
   //       7th beat: RSP_BEN=8'b01000000
   //       8th beat: RSP_BEN=8'b10000000
   //     REQ_ADDR[2:0] = 3'b001 :
   //       1st beat: RSP_BEN=8'b00000010
   //       2nd beat: RSP_BEN=8'b00000100
   //       3rd beat: RSP_BEN=8'b00001000
   //       4th beat: RSP_BEN=8'b00010000
   //       5th beat: RSP_BEN=8'b00100000
   //       6th beat: RSP_BEN=8'b01000000
   //       7th beat: RSP_BEN=8'b10000000
   //       8th beat: RSP_BEN=8'b00000001
   //     REQ_ADDR[2:0] = 3'b010 :
   //       1st beat: RSP_BEN=8'b00000100
   //       2nd beat: RSP_BEN=8'b00001000
   //       3rd beat: RSP_BEN=8'b00010000
   //       4th beat: RSP_BEN=8'b00100000
   //       5th beat: RSP_BEN=8'b01000000
   //       6th beat: RSP_BEN=8'b10000000
   //       7th beat: RSP_BEN=8'b00000001
   //       8th beat: RSP_BEN=8'b00000010
   //     REQ_ADDR[2:0] = 3'b011 :
   //     REQ_ADDR[2:0] = 3'b100 :
   //     REQ_ADDR[2:0] = 3'b101 :
   //     REQ_ADDR[2:0] = 3'b110 :
   //     REQ_ADDR[2:0] = 3'b111 :
   //   REQ_SIZE = 2'b01 : HalfWord
   //     REQ_ADDR[2:0] = 3'b000 :
   //       1st beat: RSP_BEN=8'b00000011
   //       2nd beat: RSP_BEN=8'b00001100
   //       3rd beat: RSP_BEN=8'b00110000
   //       4th beat: RSP_BEN=8'b11000000
   //       5th beat: RSP_BEN=8'b00000011
   //       6th beat: RSP_BEN=8'b00001100
   //       7th beat: RSP_BEN=8'b00110000
   //       8th beat: RSP_BEN=8'b11000000
   //     REQ_ADDR[2:0] = 3'b010 :
   //       1st beat: RSP_BEN=8'b00001100
   //       2nd beat: RSP_BEN=8'b00110000
   //       3rd beat: RSP_BEN=8'b11000000
   //       4th beat: RSP_BEN=8'b00000011
   //       5th beat: RSP_BEN=8'b00001100
   //       6th beat: RSP_BEN=8'b00110000
   //       7th beat: RSP_BEN=8'b11000000
   //       8th beat: RSP_BEN=8'b00000011
   //     REQ_ADDR[2:0] = 3'b100 :
   //     REQ_ADDR[2:0] = 3'b110 :
   //   REQ_SIZE = 2'b10 : Word
   //     REQ_ADDR[2:0] = 3'b000 :
   //       1st/3rd/5th/7th beat: RSP_BEN=8'b00001111
   //       2nd/4th/6th/8th beat: RSP_BEN=8'b11110000
   //     REQ_ADDR[2:0] = 3'b100 :
   //       1st/3rd/5th/7th beat: RSP_BEN=8'b11110000
   //       2nd/4th/6th/8th beat: RSP_BEN=8'b00001111
   //   REQ_SIZE = 2'b11 : DoubleWord
   //     REQ_ADDR[2:0] = 3'b000 :
   //       All beat: RSP_BEN=8'b11111111

   function bit [BEN_WIDTH-1:0] calc_ben;
      input [2:0]           lowaddr;
      input [1:0]           trsize;
      input [LEN_WIDTH-1:0] beat;
      bit   [LEN_WIDTH:0]   bytepos;
      begin
         if (DATA_WIDTH<=8) begin
            calc_ben = 1'b1;
         end else if (DATA_WIDTH<=16) begin
            if (trsize==2'b00) begin // Byte
               bytepos = lowaddr + beat;
               calc_ben = 2'b01 << (bytepos%2);
            end else begin
               calc_ben = 2'b11;
            end
         end else if (DATA_WIDTH<=32) begin
            if (trsize==2'b00) begin // Byte
               bytepos = lowaddr + beat;
               calc_ben = 4'h01 << (bytepos%4);
            end else if (trsize==2'b01) begin // HalfWord
               bytepos = (lowaddr[2:1] + beat) << 1;
               calc_ben = 4'h03 << (bytepos%4);
            end else begin
               calc_ben = 4'hf;
            end
         end else begin
            if (trsize==2'b00) begin // Byte
               bytepos = lowaddr + beat;
               calc_ben = 8'h01 << (bytepos%8);
            end else if (trsize==2'b01) begin // HalfWord
               bytepos = (lowaddr[2:1] + beat) << 1;
               calc_ben = 8'h03 << (bytepos%8);
            end else if (trsize==2'b10) begin // Word
               bytepos = (lowaddr[2] + beat) << 2;
               calc_ben = 8'h0f << (bytepos%8);
            end else begin
               calc_ben = 8'hff;
            end
         end
      end
   endfunction

   always @(posedge CLK or negedge RESETn) begin
      if (!RESETn) begin
         REQ_RDY  <= 1'b0;
         DEV_REQ  <= 1'b0;
         RSP_VLD  <= 1'b0;
         RSP_LAST <= 1'b0;
         RSP_DATA <= {DATA_WIDTH{1'b0}};
         buff_len <= {LEN_WIDTH{1'b0}};
         wr_ptr   <= 'b0;
         rd_ptr   <= 'b0;
         cur_addr <= 3'b0;
         cur_size <= 2'b0;
         state    <= IDLE;
         for (int i=0;i<DEPTH;i++) begin
            buffer[i] <= {DATA_WIDTH{1'b0}};
         end
      end else begin
         case (state)
           IDLE : begin
              wr_ptr   <= 'b0;
              rd_ptr   <= 'b0;
              if (REQ_VLD) begin
                 REQ_RDY  <= 1'b1;
                 buff_len <= REQ_LEN;
                 cur_addr <= REQ_ADDR[2:0];
                 cur_size <= REQ_SIZE;
                 state    <= DEV_RQST;
              end
           end
           DEV_RQST : begin
              REQ_RDY  <= 1'b0;
              DEV_REQ  <= 1'b1;
              state    <= WAIT_ACK;
           end
           WAIT_ACK : begin
              if (DEV_ACK) begin
                 buffer[wr_ptr] <= DEV_DATA;
                 if (wr_ptr==buff_len) begin
                    DEV_REQ  <= 1'b0;
                    state    <= RTRN_RSP;
                 end else begin
                    wr_ptr <= wr_ptr + 'd1;
                 end
              end
           end
           RTRN_RSP : begin
              RSP_VLD  <= 1'b1;
              RSP_DATA <= buffer[rd_ptr];
              RSP_BEN  <= calc_ben(cur_addr, cur_size, rd_ptr);
              if (rd_ptr==buff_len) begin
                 RSP_LAST <= 1'b1;
              end
              state <= WAIT_RDY;
           end
           WAIT_RDY : begin
              if (RSP_RDY) begin
                 if (rd_ptr==buff_len) begin
                    RSP_VLD  <= 1'b0;
                    RSP_LAST <= 1'b0;
                    state    <= IDLE;
                 end else begin
                    RSP_DATA <= buffer[rd_ptr+'d1];
                    RSP_BEN  <= calc_ben(cur_addr, cur_size, (rd_ptr+'d1));
                    if ((rd_ptr+'d1)==buff_len) begin
                       RSP_LAST <= 1'b1;
                    end
                    rd_ptr <= rd_ptr + 'd1;
                 end
              end
           end
           default : begin
              REQ_RDY  <= 1'b0;
              DEV_REQ  <= 1'b0;
              RSP_VLD  <= 1'b0;
              buff_len <= {LEN_WIDTH{1'b0}};
              wr_ptr   <= 'b0;
              rd_ptr   <= 'b0;
              state    <= IDLE;
           end
         endcase
      end
   end

endmodule // ctrl
