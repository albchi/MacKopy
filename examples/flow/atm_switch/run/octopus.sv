/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

//
//      Copyright (c) 2000 by Qualis Design Corporation. All rights reserved.
//      
//
//      This file contains licensed materials and may used and distributed
//      provided that this copyright statement is not removed from the file
//      and that any derivative work contains this copyright notice.
//
//      Qualis Design Corporation            Synopsys, Inc.
//      http://www.qualis.com                http://www.synopsys.com
//
// Description:
//      Top-level module for the Octopus behavioral model
//
// Author:      $Author: badri $
// Revision:    $Revision: 1.1 $
//

`resetall

`include "interface.svh"

module octopus(
               //
               // Input Utopia interfaces x 8
               //Feature: modport
               //  using the tx modport for direction
               atm_interface.rx rx_0,
               atm_interface.rx rx_1,
               atm_interface.rx rx_2,
               atm_interface.rx rx_3,
               atm_interface.rx rx_4,
               atm_interface.rx rx_5,
               atm_interface.rx rx_6,
               atm_interface.rx rx_7,
               //
               // Output Utopia interfaces x 8
               //  using the tx modport for direction
               atm_interface.tx tx_0,
               atm_interface.tx tx_1,
               atm_interface.tx tx_2,
               atm_interface.tx tx_3,
               atm_interface.tx tx_4,
               atm_interface.tx tx_5,
               atm_interface.tx tx_6,
               atm_interface.tx tx_7,

               //
               // Miscellaneous pins
               //
               input logic clk,
               input logic rst);

reg  [7:0]  sc_vpi;
reg  [15:0] sc_mask;

reg  [7:0]  qos_vpi;
reg  [15:0] qos_data;

//
// Switching context memory
//
reg [15:0] sc_mem [7:0];
reg sc_in_use;
 
//
// Quality-of-Service memory
//
reg [15:0] qos_mem [7:0];
reg qos_in_use;

//
// Reset task
//
initial reset;
task reset;
begin
   RX[0].atm_rx.reset;
   TX[0].atm_tx.reset;
   disable SWITCH_LOGIC[0].input_port;
   RX[1].atm_rx.reset;
   TX[1].atm_tx.reset;
   disable SWITCH_LOGIC[1].input_port;
   RX[2].atm_rx.reset;
   TX[2].atm_tx.reset;
   disable SWITCH_LOGIC[2].input_port;
   RX[3].atm_rx.reset;
   TX[3].atm_tx.reset;
   disable SWITCH_LOGIC[3].input_port;
   RX[4].atm_rx.reset;
   TX[4].atm_tx.reset;
   disable SWITCH_LOGIC[4].input_port;
   RX[5].atm_rx.reset;
   TX[5].atm_tx.reset;
   disable SWITCH_LOGIC[5].input_port;
   RX[6].atm_rx.reset;
   TX[6].atm_tx.reset;
   disable SWITCH_LOGIC[6].input_port;
   RX[7].atm_rx.reset;
   TX[7].atm_tx.reset;
   disable SWITCH_LOGIC[7].input_port;
   disable arbiter;
end
endtask

always
begin
   wait (rst === 1'b1 && clk === 1'b1);
   reset;
   wait (rst === 1'b0);
end

//
// Switching Context Memory Read/Write
//
initial sc_reset;
task sc_reset;
begin
   sc_in_use = 1'b0;
   sc_vpi  <= 7'bx ;
   sc_mask <= 15'bz ;
end
endtask


task sc_read;
   input  [ 7:0] sc_vpi ;
   output [15:0] sc_mask ;
begin

   if (sc_in_use) begin
      $write("FATAL: Concurrent invocation of Switching Context Memory.\n");
      $finish;
   end
   sc_in_use = 1'b1;

   @ (negedge clk);
   //sc_mask = sc_mem[sc_vpi]; //read from behavioral memory
   read_mem(sc_vpi,sc_mask); //read from memory subsystem

   sc_in_use = 1'b0;
end
endtask


task sc_write;
   input [ 7:0] sc_vpi ;
   input [15:0] sc_mask ;
begin
   if (sc_in_use) begin
      $write("FATAL: Concurrent invocation of Switching Context Memory\n");
      $finish;
   end
   sc_in_use = 1'b1;

   @ (negedge clk);
      $write("WRITING: Switching Context Memory\n");
      //  sc_mem[sc_vpi] = sc_mask; //write to behavioral memory
      write_mem(sc_vpi,sc_mask); //write to memory subsystem
      $write("DONE: Switching Context Memory\n");

   sc_in_use = 1'b0;
end
endtask

//
// QoS Memory Read/Write  
//
initial qos_reset;
task qos_reset;
begin
   qos_in_use = 1'b0;
   qos_vpi  <= 7'bx ;
   qos_data <= 15'bz ;
end
endtask
 
 
task qos_read;
   input  [ 7:0] qos_vpi ;
   output [15:0] qos_data ;
begin
   if (qos_in_use) begin
      $write("FATAL: Concurrent invocation of QoS Memory.\n");
      $finish;
   end
   qos_in_use = 1'b1;
 
   @ (negedge clk);
   qos_data = qos_mem[qos_vpi];
 
   if ($test$plusargs("debug"))
      $display("Time[%0t] qos_read of qos_mem: addr %0h data %0h",
        $time,
        qos_vpi,
        qos_data);
   qos_in_use = 1'b0;
end
endtask
 
 
task qos_write;
   input [ 7:0] qos_vpi ;
   input [15:0] qos_data ;
begin
   if (qos_in_use) begin
      $write("FATAL: Concurrent invocation of QoS Memory\n");
      $finish;
   end
   qos_in_use = 1'b1;
 
   @ (negedge clk);
   qos_mem[qos_vpi] = qos_data;
   if ($test$plusargs("debug"))
      $display("Time[%0t] qos_read of qos_mem: addr %0h data %0h",
        $time,
        qos_vpi,
        qos_data);
 
   qos_in_use = 1'b0;
end
endtask

//
// Arbiter for mutually exclusive region
//

reg [9:0] request;
integer owner;
always
begin: arbiter
   integer last_winner;
   
   request     = 10'h000;
   owner       = 'bx;
   last_winner = 9;

   forever begin: select_winner
      integer winner;

      // Wait for a request
      wait (request !== 10'h000);

      // Find the next winner, in a
      // fair, round-robin fashion
      winner = (last_winner + 1) % 10;
      repeat (10) begin
         // Do we have a winner?
         if (request[winner]) begin
            owner = winner;
            wait (request[winner] === 1'b0);
            owner = 'bx;
            last_winner = winner;
            disable select_winner;
         end
         winner = (winner + 1) % 10;
      end

      // We should NEVER get here!
      $write("FATAL: %M: Internal error (%b)!!\n", request);
      $finish;
   end
end

//
//Feature: Use generates and MDA's to reduce size of this block.
//
// ATM-layer Utopia interface receivers
//

generate
  genvar gv;
  for (gv = 0; gv <= 7; gv = gv + 1) begin: RX
     case(gv) 
	   0: utopia_atm_rx atm_rx(rx_0);
	   1: utopia_atm_rx atm_rx(rx_1);
	   2: utopia_atm_rx atm_rx(rx_2);
	   3: utopia_atm_rx atm_rx(rx_3);
	   4: utopia_atm_rx atm_rx(rx_4);
	   5: utopia_atm_rx atm_rx(rx_5);
	   6: utopia_atm_rx atm_rx(rx_6);
	   7: utopia_atm_rx atm_rx(rx_7);
     endcase
  end
endgenerate
    
//
// ATM-layer Utopia interface transmitters
//
generate
  genvar gv;
  for (gv = 0; gv <= 7; gv = gv + 1) begin: TX
     case(gv) 
	   0: utopia_atm_tx atm_tx(tx_0);
	   1: utopia_atm_tx atm_tx(tx_1);
	   2: utopia_atm_tx atm_tx(tx_2);
	   3: utopia_atm_tx atm_tx(tx_3);
	   4: utopia_atm_tx atm_tx(tx_4);
	   5: utopia_atm_tx atm_tx(tx_5);
	   6: utopia_atm_tx atm_tx(tx_6);
	   7: utopia_atm_tx atm_tx(tx_7);
     endcase
  end
endgenerate

//
// Switching logic
//
reg [7:0] filter [0:7];
reg [7:0] cast [0:7];

generate
  genvar gv;
  for (gv = 0; gv <= 7; gv = gv + 1) begin: ATM_CELL
    atm_cell atm_cell();
  end
  for (gv = 0; gv <= 7; gv = gv + 1) begin: SWITCH_LOGIC
	always
	begin: input_port
	   reg [53*8:1] cell;
	   reg          valid;

		#1;

	   RX[gv].atm_rx.get_cell(RX[gv].atm_rx.BLOCKING, cell, valid);
	   // This should never happen in BLOCKING mode
	   if (valid !== 1'b1) begin
		  $write("ERROR: %M: Rx'ed cell on port #0 is not valid\n");
		  disable input_port;
	   end
	   ATM_CELL[gv].atm_cell.from_bits(cell);

	   // If the HEC is bad, drop the cell
	   if (! ATM_CELL[gv].atm_cell.check_hec(0)) begin
		  disable SWITCH_LOGIC[gv].input_port;
	   end

	   //
	   // Mutually exclusive region
	   //

	   begin: region
		  request[gv] = 1'b1;
		  fork: wait4
			 wait (owner === gv) disable wait4;
			 begin
				repeat (1000) @ (posedge clk);
				$write("%M: Cannot obtain memory interface\n");
				$finish;
			 end
		  join
		  
		  // Get the switching information for this cell's VPI
		  sc_read(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, {filter[gv], cast[gv]});
		  
		  // Is this cell filtered out?
		  if (filter[gv][gv]) begin
			 disable region;
		  end
		  
		  // Forward this cell to the appropriate
		  // output ports
		  if (cast[gv][0]) begin
			 TX[gv].atm_tx.put_cell(TX[gv].atm_tx.NON_BLOCK,
								cell, valid);
			 // Was the cell dropped?
			 if (valid !== 1'b1) begin: QoS_0
				reg [15:0] count;

				qos_read(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
				count = count + 1;
				qos_write(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
			 end: QoS_0
		  end
		  if (cast[gv][1]) begin
			 TX[gv].atm_tx.put_cell(TX[gv].atm_tx.NON_BLOCK,
								cell, valid);
			 // Was the cell dropped?
			 if (valid !== 1'b1) begin: QoS_1
				reg [15:0] count;

				qos_read(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
				count = count + 1;
				qos_write(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
			 end: QoS_1
		  end
		  if (cast[gv][2]) begin
			 TX[gv].atm_tx.put_cell(TX[gv].atm_tx.NON_BLOCK,
								cell, valid);
			 // Was the cell dropped?
			 if (valid !== 1'b1) begin: QoS_2
				reg [15:0] count;

				qos_read(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
				count = count + 1;
				qos_write(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
			 end: QoS_2
		  end
		  if (cast[gv][3]) begin
			 TX[gv].atm_tx.put_cell(TX[gv].atm_tx.NON_BLOCK,
								cell, valid);
			 // Was the cell dropped?
			 if (valid !== 1'b1) begin: QoS_3
				reg [15:0] count;

				qos_read(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
				count = count + 1;
				qos_write(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
			 end: QoS_3
		  end
		  if (cast[gv][4]) begin
			 TX[gv].atm_tx.put_cell(TX[gv].atm_tx.NON_BLOCK,
								cell, valid);
			 // Was the cell dropped?
			 if (valid !== 1'b1) begin: QoS_4
				reg [15:0] count;

				qos_read(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
				count = count + 1;
				qos_write(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
			 end: QoS_4
		  end
		  if (cast[gv][5]) begin
			 TX[gv].atm_tx.put_cell(TX[gv].atm_tx.NON_BLOCK,
								cell, valid);
			 // Was the cell dropped?
			 if (valid !== 1'b1) begin: QoS_5
				reg [15:0] count;

				qos_read(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
				count = count + 1;
				qos_write(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
			 end: QoS_5
		  end
		  if (cast[gv][6]) begin
			 TX[gv].atm_tx.put_cell(TX[gv].atm_tx.NON_BLOCK,
								cell, valid);
			 // Was the cell dropped?
			 if (valid !== 1'b1) begin: QoS_6
				reg [15:0] count;

				qos_read(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
				count = count + 1;
				qos_write(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
			 end: QoS_6
		  end
		  if (cast[gv][7]) begin
			 TX[gv].atm_tx.put_cell(TX[gv].atm_tx.NON_BLOCK,
								cell, valid);
			 // Was the cell dropped?
			 if (valid !== 1'b1) begin: QoS_7
				reg [15:0] count;

				qos_read(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
				count = count + 1;
				qos_write(ATM_CELL[gv].atm_cell.atm_cell_i.header_i.vpi, count);
			 end: QoS_7
		  end
	   end: region
	   //feature: named ending blocks

	   //
	   // End of mutually exclusive region
	   //
	   request[gv] = 1'b0;
	   wait (owner !== gv);
	end: input_port
  end
endgenerate

//instantiate memory sub-system
  wire [7:0] busData;
  wire [7:0] ramData;

  wire [5:0] ramAddr;
  wire rdWr_N;
  wire ce0_N;
  wire ce1_N;
  wire ce2_N;
  wire ce3_N;

  reg busRdWr_N;
  reg adxStrb;
  reg [7:0] busAddr;

`include "cntrlr_tasks.v"


   sram s0 (/*AUTOINST*/
	    // Inouts
	    .ramData			(ramData[7:0]),
	    // Inputs
	    .ce_N			(ce0_N),
	    .rdWr_N			(rdWr_N),
	    .ramAddr			(ramAddr[5:0]));
   sram s1 (/*AUTOINST*/
	    // Inouts
	    .ramData			(ramData[7:0]),
	    // Inputs
	    .ce_N			(ce1_N),
	    .rdWr_N			(rdWr_N),
	    .ramAddr			(ramAddr[5:0]));
   sram s2 (/*AUTOINST*/
	    // Inouts
	    .ramData			(ramData[7:0]),
	    // Inputs
	    .ce_N			(ce2_N),
	    .rdWr_N			(rdWr_N),
	    .ramAddr			(ramAddr[5:0]));
   sram s3 (/*AUTOINST*/
	    // Inouts
	    .ramData			(ramData[7:0]),
	    // Inputs
	    .ce_N			(ce3_N),
	    .rdWr_N			(rdWr_N),
	    .ramAddr			(ramAddr[5:0]));
   
   cntrlr cntrlr_i(/*AUTOINST*/
		   // Outputs
		   .rdWr_N		(rdWr_N),
		   .ce0_N		(ce0_N),
		   .ce1_N		(ce1_N),
		   .ce2_N		(ce2_N),
		   .ce3_N		(ce3_N),
		   .ramAddr		(ramAddr[5:0]),
		   // Inouts
		   .busData		(busData[7:0]),
		   .ramData		(ramData[7:0]),
		   // Inputs
		   .clk			(clk),
		   .reset		(rst),
		   .busRdWr_N		(busRdWr_N),
		   .adxStrb		(adxStrb),
		   .busAddr		(busAddr[7:0]));

endmodule

