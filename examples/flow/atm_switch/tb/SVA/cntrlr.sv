/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

module memory_checker (input clk, input reset, input rdWr_N,
                     input ce0_N,input ce1_N,input ce2_N,input ce3_N,
                     input adxStrb, input busRdWr_N, input [7:0] busData,
          	     input [7:0] ramData,input [7:0] busAddr,input [5:0] ramAddr


); 





  //Booleans and Latched variable values
`define ce_mutex  (ce0_N || (ce1_N && ce2_N && ce3_N)) && (ce1_N || (ce2_N && ce3_N)) && (ce2_N || ce3_N) 
`define true 1'b1

  wire ce_idle = ( (ce0_N && ce1_N && ce2_N && ce3_N) );
  wire reading = adxStrb && busRdWr_N && !reset;
  wire writing = adxStrb && !busRdWr_N && !reset;
  reg [7:0] addr_in; initial addr_in = 8'b0; 
  always @(posedge clk) addr_in <= adxStrb ? busAddr : addr_in;
  reg [7:0] read_data; initial read_data = 8'b0; 
  always @(posedge clk) read_data <= (!ce_idle && rdWr_N) ? ramData : read_data;
  reg [7:0] write_data; initial write_data = 8'b0; 
  always @(posedge clk) write_data <= writing ? busData : write_data;

  wire ce_mutex2 = (ce0_N || (ce1_N && ce2_N && ce3_N)) && (ce1_N || (ce2_N && ce3_N)) && (ce2_N || ce3_N);


// no ce active and no write until first adxStrb
  property e_after_reset;
    @(posedge clk) ($fell( reset )) |-> ((ce_idle && rdWr_N) throughout ##[0:$] adxStrb);
  endproperty

// rdWr_N is a one clk cycle wide pulse
  property e_rdWr_N_pulse;
    @(posedge clk) (!rdWr_N && !reset) |-> (##1 rdWr_N);
  endproperty

// ce's are mutually exclusive
  property e_ce_mutex;
    @(posedge clk) (!reset) |-> (##0 (`ce_mutex));
  endproperty

// ce's are mutually exclusive
  property e_ce_mutex2;
    @(posedge clk) (!reset) |-> ce_mutex2;
  endproperty

// ce is a one clk cycle wide pulse
  property e_ce_pulse;
    @(posedge clk) (!ce_idle && !reset) |-> ##1 ce_idle;
  endproperty

// after a ce is active, all must stay idle untilnext adxStrb
  property e_no_ce_till_strb;
    @(posedge clk) ($rose( ce_idle )) |-> ce_idle [*1:$] ##1 adxStrb;
  endproperty


// Address is transferred correctly to the memory I/F
  property e_addr_ok;
    @(posedge clk) (!ce_idle && !reset) |-> ramAddr == (addr_in[5:0]);
  endproperty

// a ce is active 2 cycles  after reading command
  property e_ce_on_read;
    @(posedge clk) reading |-> (!ce_idle)[*2] ##1 !ce_idle;
  endproperty

// a ce_ is active for 1 cycle 3 cycles after writing command
  property e_ce_on_write;
    @(posedge clk) writing |-> ce_idle [*3] ##1 !ce_idle;
  endproperty

// ramRdWr_N is 0 3 cycles after writing
  property e_rdWr_N_on_write;
    @(posedge clk) writing |-> rdWr_N [*3] ##1 !rdWr_N;
  endproperty

// ram address is stable and correct 1 cycle after writing
// and for 4 cycles
  property e_wr_addr_stable;
    @(posedge clk) writing |-> ##1 ((ramAddr == addr_in[5:0]) [*4]);
  endproperty

// read data appears 3 cycles after adxStrb
  property e_rd_data_ok;
    @(posedge clk) reading |-> ##3 (busData === read_data);
  endproperty

// rdWr_N is 1 after 0 until adxStrb
  property e_rdWr_N_idle;
    @(posedge clk) $rose( rdWr_N ) |-> rdWr_N [*0:$] ##1 adxStrb;
  endproperty

// ram address is stable and rdWr_N for two cycles, 
// one cycle after adxStrb
// some redundancy with the Global address check
  property e_rd_addr_stable;
    @(posedge clk) reading |-> ##1 ((rdWr_N && (ramAddr === addr_in[5:0]))[*2]);
  endproperty

// Address is corectly  decoded to ce's
  property e_ce0_decode;
    @(posedge clk) !ce_idle && !reset |-> !ce0_N && (addr_in[7:6] == 2'b00) or !ce1_N && (addr_in[7:6] == 2'b01) || !ce2_N && (addr_in[7:6] == 2'b10) || !ce3_N && (addr_in[7:6] == 2'b11);
  endproperty

// ramData is stable and correct 2 cycles after writing for 3 cycles
  property e_write_data_ok;
    @(posedge clk) writing |-> ##2 ((ramData === write_data) [*2]);
  endproperty


  c_after_reset: assert property( e_after_reset );
  c_rdWr_N_pulse: assert property( e_rdWr_N_pulse );
  c_ce_mutex: assert property( e_ce_mutex );
  c_ce_mutex2: assert property( e_ce_mutex2 );
  c_ce_pulse: assert property( e_ce_pulse );
  c_no_ce_till_strb: assert property( e_no_ce_till_strb );
  c_addr_ok: assert property( e_addr_ok );
  c_ce_on_read: assert property( e_ce_on_read );
  c_ce_on_write: assert property( e_ce_on_write );
  c_rdWr_N_on_write: assert property( e_rdWr_N_on_write );
  c_wr_addr_stable: assert property( e_wr_addr_stable );
  c_rd_data_ok: assert property( e_rd_data_ok );
  c_rdWr_N_idle: assert property( e_rdWr_N_idle );
  c_rd_addr_stable: assert property( e_rd_addr_stable );
  c_ce0_decode: assert property( e_ce0_decode );
  c_write_data_ok: assert property( e_write_data_ok );


endmodule


bind th.duv.cntrlr_i memory_checker memory_checker1(clk,reset,rdWr_N,ce0_N,ce1_N,ce2_N,ce3_N,adxStrb,busRdWr_N,busData,ramData,busAddr,ramAddr); 
