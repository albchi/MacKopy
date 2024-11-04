/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

module cntrlr(clk, reset, busAddr, busData, busRdWr_N, adxStrb, rdWr_N, ce0_N,
	ce1_N, ce2_N, ce3_N, ramAddr, ramData);

input clk, reset, busRdWr_N, adxStrb; 
input [7:0] busAddr;
inout [7:0] busData;
output rdWr_N, ce0_N, ce1_N, ce2_N, ce3_N;
output [5:0] ramAddr;
inout [7:0] ramData;

typedef enum reg[1:0] {IDLE=0, START, WRITE0, WRITE1} e_states;

e_states state, nxState;
wire nxvalid;
reg valid;
reg[3:0] nxCe_, ce_;
reg nxRdWr_, rdWr_N;
reg outEn;
reg [7:0] dataWr, dataRd, address;
reg busOe, readWrite_;


/** IO PADS for bidirectionals ***/
wire[1:0] bruce = state;

assign  ramData = (outEn) ? dataWr : 8'bzzzzzzzz;
assign busData = (busOe) ? dataRd : 8'bzzzzzzzz;

assign ce0_N = ce_[0];
assign ce1_N = ce_[1];
assign ce2_N = ce_[2];
assign ce3_N = ce_[3];

assign ramAddr = address[5:0];

always_comb
begin 
   //ova one_hot(1, posedge clk, ce_, 1, "dfdfdfdfd");
   nxState = state;
   nxCe_ = ce_;
   nxRdWr_ = 1'b1;
   outEn = 1'b0;

   case(state)
      IDLE: begin
         if(valid)
            nxState = START;
 	 if(valid & readWrite_) begin
	    case(address[7:6])
	       2'b00: nxCe_= 4'b1110;
	       2'b01: nxCe_= 4'b1101;
	       2'b10: nxCe_= 4'b1011;
	       2'b11: nxCe_= 4'b0111;
	    endcase
	 end
	 else nxCe_ = 4'b1111;
      end

      START: begin
         if(readWrite_) begin // read operation
  	    nxState = IDLE;
	    nxCe_ = 4'b1111;
         end
	 else begin  // write operation
  	    nxRdWr_ = 1'b0;         
	    case(address[7:6])
	       2'b00: nxCe_= 4'b1110;
	       2'b01: nxCe_= 4'b1101;
	       2'b10: nxCe_= 4'b1011;
	       2'b11: nxCe_= 4'b0111;
	    endcase
            outEn = 1'b1;
  	    nxState = WRITE0;
	 end
      end

      WRITE0: begin
	 nxRdWr_ = 1'b1;         
	 outEn = 1'b1;
	 nxCe_ = 4'b1111;
	 nxState = WRITE1;
      end
 
      WRITE1: begin
	 outEn = 1'b1;
         nxState = IDLE;
      end

   endcase
end

`ifdef INLINE_SVA
//Assert that rdWr_N is a one clk cycle wide pulse
  property p_rdWr_N_pulse;
    @(posedge clk) (!rdWr_N && !reset) |-> (##1 rdWr_N);
  endproperty
  s_rdWr_N_pulse: assert property( p_rdWr_N_pulse );

// Assert that ram address is stable and correct 1 cycle after writing
// and for 4 cycles
  reg [7:0] addr_in; initial addr_in = 8'b0; 
  always @(posedge clk) addr_in <= adxStrb ? busAddr : addr_in;
  wire writing = adxStrb && !busRdWr_N && !reset;
  property p_wr_addr_stable;
    @(posedge clk) writing |-> ##1 ((ramAddr == addr_in[5:0]) [*4]);
  endproperty
  s_wr_addr_stable: assert property( p_wr_addr_stable );
`endif


assign nxvalid = adxStrb & (state == IDLE); // diregard other stuff while busy 

always_ff @(posedge clk)
begin
   if(reset)
      state <= #1 IDLE;
   else begin
      state <= #1 nxState;
   end

   address <= #1 (nxvalid) ? busAddr : address;
   dataWr <= #1 (nxvalid & ~busRdWr_N) ? busData : dataWr;
   readWrite_ <= #1 (nxvalid) ? busRdWr_N : readWrite_;
   ce_ <= #1 nxCe_;
   rdWr_N <= #1 nxRdWr_; 
   dataRd <= #1 (rdWr_N & ~&ce_) ? ramData : dataRd;
   busOe <= #1 (rdWr_N & ~&ce_);
   valid <= #1 nxvalid;
end

initial
begin
  /* 
  $monitor($time,,"%b %b %b %b %b %b %b %b %b", reset, state, adxStrb, 
	ce_, rdWr_N, ramAddr, ramData, busAddr, busData);
  */
end
endmodule
