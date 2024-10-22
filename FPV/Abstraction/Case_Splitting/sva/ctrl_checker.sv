module ctrl_checker
  #(parameter DATA_WIDTH = 64,
    parameter ADDR_WIDTH = 20,
    parameter LEN_WIDTH  = 3,
    parameter BEN_WIDTH  = (DATA_WIDTH/8),
    parameter DATA_INTEG = 1, // 1: Data Integrity assertions only
    parameter SPLIT_MODE = 0) // 0: both, 1: non case-split, 2: case-split
   (input logic                  CLK,
    input logic                  RESETn,
    input logic [ADDR_WIDTH-1:0] REQ_ADDR,
    input logic [LEN_WIDTH-1:0]  REQ_LEN,
    input logic [1:0]            REQ_SIZE,
    input logic                  REQ_VLD,
    input logic                  REQ_RDY,
    input logic                  RSP_LAST,
    input logic                  RSP_VLD,
    input logic                  RSP_RDY,
    input logic [BEN_WIDTH-1:0]  RSP_BEN,
    input logic [DATA_WIDTH-1:0] RSP_DATA,
    input logic                  DEV_REQ,
    input logic                  DEV_ACK,
    input logic [DATA_WIDTH-1:0] DEV_DATA);

   localparam RSP_LENGTH = 'b1 << LEN_WIDTH;

   bit [LEN_WIDTH-1:0]  req_counts, rsp_counts, dev_counts;
   bit [DATA_WIDTH-1:0] dev_data_q [0:RSP_LENGTH-1];
   bit [ADDR_WIDTH-1:0] rqst_addr;
   bit [1:0]            rqst_size;
   bit [BEN_WIDTH-1:0]  exp_rsp_ben;
   bit [BEN_WIDTH-1:0]  byte_rsp_ben;
   bit [BEN_WIDTH-1:0]  hword_rsp_ben;
   bit [BEN_WIDTH-1:0]  word_rsp_ben;
   bit [BEN_WIDTH-1:0]  dword_rsp_ben;
   bit [DATA_WIDTH-1:0] valid_byte_lanes;
   bit [2:0]            symb_bit;
   bit [7:0]            data_byte_lanes [0:BEN_WIDTH-1];

   always @(posedge CLK or negedge RESETn) begin
      if (!RESETn) begin
         req_counts <= {RSP_LENGTH{1'b0}};
         rsp_counts <= {RSP_LENGTH{1'b0}};
         dev_counts <= {RSP_LENGTH{1'b0}};
         rqst_addr  <= {ADDR_WIDTH{1'b0}};
         rqst_size  <= 2'b0;
         for (int i=0;i<RSP_LENGTH;i++) begin
            dev_data_q[i] <= {DATA_WIDTH{1'b0}};
         end
      end else begin
         if (REQ_VLD && REQ_RDY) begin
            req_counts <= REQ_LEN;
            rqst_addr  <= REQ_ADDR;
            rqst_size  <= REQ_SIZE;
            rsp_counts <= {RSP_LENGTH{1'b0}};
            dev_counts <= {RSP_LENGTH{1'b0}};
         end else begin
            if (RSP_VLD && RSP_RDY) begin
               rsp_counts <= rsp_counts + 'd1;
            end
            if (DEV_REQ && DEV_ACK) begin
               dev_data_q[dev_counts] <= DEV_DATA;
               dev_counts <= dev_counts + 'd1;
            end
         end
      end
   end

   property p_rsp_last_not_early;
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && rsp_counts<req_counts) |-> !RSP_LAST;
   endproperty

   property p_rsp_last_not_late;
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && rsp_counts==req_counts) |-> RSP_LAST;
   endproperty

   property p_rsp_last_not_early_per_beat(beat);
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && rsp_counts==beat && beat<req_counts) |-> !RSP_LAST;
   endproperty

   property p_rsp_last_not_late_per_beat(beat);
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && rsp_counts==beat && beat==req_counts) |-> RSP_LAST;
   endproperty

   property p_rsp_data_stable;
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && !RSP_RDY) |=> $stable((RSP_DATA & valid_byte_lanes));
   endproperty

   property p_rsp_data_stable_per_byte(idx);
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && !RSP_RDY) |=> $stable(data_byte_lanes[idx]);
   endproperty

   property p_rsp_data_integrity;
      @(posedge CLK) disable iff (!RESETn)
        RSP_VLD |-> (RSP_DATA==dev_data_q[rsp_counts]);
   endproperty

   property p_rsp_data_integrity_per_beat(beat);
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && rsp_counts==beat) |-> (RSP_DATA==dev_data_q[beat]);
   endproperty

   property p_rsp_ben_expected;
      @(posedge CLK) disable iff (!RESETn)
        RSP_VLD |-> (RSP_BEN==exp_rsp_ben);
   endproperty

   property p_rsp_ben_expected_byte;
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && rqst_size==2'b00) |-> (RSP_BEN==byte_rsp_ben);
   endproperty

   property p_rsp_ben_expected_hword;
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && rqst_size==2'b01) |-> (RSP_BEN==hword_rsp_ben);
   endproperty

   property p_rsp_ben_expected_word;
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && rqst_size==2'b10) |-> (RSP_BEN==word_rsp_ben);
   endproperty

   property p_rsp_ben_expected_dword;
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && rqst_size==2'b11) |-> (RSP_BEN==dword_rsp_ben);
   endproperty

generate
   if (SPLIT_MODE inside {0, 1}) begin : NOSPLIT

      // the maximum size is DoubleWord, i.e., DATA_WIDTH<=64
      function bit [BEN_WIDTH-1:0] get_exp_ben;
         input [2:0]           addr; // [2:0] represents up to DATA_WIDTH=64
         input [1:0]           size;
         input [LEN_WIDTH-1:0] beat;
         bit   [2:0]           num_bytes;
         bit   [LEN_WIDTH+2:0] txn_bytes;
         bit   [2:0]           align_addr;
         bit   [LEN_WIDTH+2:0] beat_addr;
         begin
            num_bytes = 'b1 << size;
            txn_bytes = beat << size;
            align_addr = (addr >> size) << size;
            beat_addr = align_addr + txn_bytes;
            if (size==2'b00) begin // Byte
               get_exp_ben = 'b1 << beat_addr[2:0];
            end else if (size==2'b01) begin // HalfWord
               get_exp_ben = 'b11 << beat_addr[2:0];
            end else if (size==2'b10) begin // Word
               get_exp_ben = 'b1111 << beat_addr[2:0];
            end else begin
               get_exp_ben = 8'b11111111;
            end
         end
      endfunction

      assign exp_rsp_ben = get_exp_ben(rqst_addr, rqst_size, rsp_counts);

      always_comb begin
         valid_byte_lanes = 'b0;
         if (RSP_VLD) begin
            for (int i=(BEN_WIDTH-1);i>=0;i--) begin
               valid_byte_lanes = valid_byte_lanes << 8;
               if (exp_rsp_ben[i]==1'b1) begin
                  valid_byte_lanes[7:0] = 8'hff;
               end
            end
         end
      end

      if (DATA_INTEG==0) begin : ALLAST
         ast_rsp_data_stable    : assert property(p_rsp_data_stable);
         ast_rsp_last_not_early : assert property(p_rsp_last_not_early);
         ast_rsp_last_not_late  : assert property(p_rsp_last_not_late);
         ast_rsp_ben_expected   : assert property(p_rsp_ben_expected);
      end : ALLAST

      ast_rsp_data_integrity : assert property(p_rsp_data_integrity);

   end : NOSPLIT
   if (SPLIT_MODE inside {0, 2}) begin : SPLIT

      bit [LEN_WIDTH+2:0] beat_addr;
      //bit [2:0]           num_bytes;

      //assign num_bytes = 'b1 << rqst_size;
      assign beat_addr = rqst_addr + (rsp_counts << rqst_size);

      always_comb begin
         if (DATA_WIDTH<=8) begin
            byte_rsp_ben  = 1'b1;
            hword_rsp_ben = 1'b0;
            word_rsp_ben  = 1'b0;
            dword_rsp_ben = 1'b0;
         end else 
         if (DATA_WIDTH<=16) begin
            byte_rsp_ben  = 2'b01 << beat_addr[0];
            hword_rsp_ben = 2'b11;
            word_rsp_ben  = 2'b0;
            dword_rsp_ben = 2'b0;
         end else 
         if (DATA_WIDTH<=32) begin
            byte_rsp_ben  = 4'b0001 << beat_addr[1:0];
            //hword_rsp_ben = 4'b0011 << (beat_addr[1]<<1);
            hword_rsp_ben = 4'b0011 << (beat_addr[1]*2);
            word_rsp_ben  = 4'b1111;
            dword_rsp_ben = 4'b0;
         end else begin
            byte_rsp_ben  = 8'b00000001 << beat_addr[2:0];
            //hword_rsp_ben = 8'b00000011 << (beat_addr[2:1]<<1);
            hword_rsp_ben = 8'b00000011 << (beat_addr[2:1]*2);
            //word_rsp_ben  = 8'b00001111 << (beat_addr[2]<<2);
            word_rsp_ben  = 8'b00001111 << (beat_addr[2]*4);
            dword_rsp_ben = 8'b11111111;
         end
      end

      bit [DATA_WIDTH-1:0] tmp_data;

      always_comb begin
         tmp_data = RSP_DATA;
         for (int i=0;i<BEN_WIDTH;i++) begin
            data_byte_lanes[i] = tmp_data[7:0];
            tmp_data = tmp_data >> 8;
         end
      end

      asm_symb_bit_stable : assume property
         (@(posedge CLK) disable iff (!RESETn)
            $stable(symb_bit));

      if (DATA_INTEG==0) begin : ALLAST
         for (genvar i=0;i<BEN_WIDTH;i++) begin : PERBYTE
            ast_rsp_data_stable_per_byte    : assert property(p_rsp_data_stable_per_byte(i));
         end : PERBYTE
         for (genvar i=0;i<(RSP_LENGTH-1);i++) begin : PERBEATER
            ast_rsp_last_not_early_per_beat : assert property(p_rsp_last_not_early_per_beat(i));
         end : PERBEATER
         for (genvar i=0;i<RSP_LENGTH;i++) begin : PERBEAT
            ast_rsp_last_not_late_per_beat  : assert property(p_rsp_last_not_late_per_beat(i));
         end : PERBEAT

         ast_rsp_ben_expected_byte  : assert property(p_rsp_ben_expected_byte);
         ast_rsp_ben_expected_hword : assert property(p_rsp_ben_expected_hword);
         ast_rsp_ben_expected_word  : assert property(p_rsp_ben_expected_word);
         ast_rsp_ben_expected_dword : assert property(p_rsp_ben_expected_dword);
      end : ALLAST

      for (genvar i=0;i<RSP_LENGTH;i++) begin : DATINTEG
         ast_rsp_data_integrity_per_beat : assert property(p_rsp_data_integrity_per_beat(i));
      end : DATINTEG

   end : SPLIT

endgenerate

   // Common assertions
   property p_rsp_vld_stable;
      @(posedge CLK) disable iff (!RESETn)
        (RSP_VLD && !RSP_RDY) |=> RSP_VLD;
   endproperty

   property p_dev_req_stable;
      @(posedge CLK) disable iff (!RESETn)
        (DEV_REQ && !DEV_ACK) |=> DEV_REQ;
   endproperty

   ast_rsp_vld_stable : assert property(p_rsp_vld_stable);
   ast_dev_req_stable : assert property(p_dev_req_stable);

   // Common constraints
   property p_req_vld_stable;
      @(posedge CLK) disable iff (!RESETn)
        (REQ_VLD && !REQ_RDY) |=> REQ_VLD;
   endproperty

   property p_req_sig_stable(sig);
      @(posedge CLK) disable iff (!RESETn)
        (REQ_VLD && !REQ_RDY) |=> $stable(sig);
   endproperty

   asm_req_vld_stable  : assume property(p_req_vld_stable);
   asm_req_len_stable  : assume property(p_req_sig_stable(REQ_LEN));
   asm_req_addr_stable : assume property(p_req_sig_stable(REQ_ADDR));
   asm_req_size_stable : assume property(p_req_sig_stable(REQ_SIZE));

endmodule
