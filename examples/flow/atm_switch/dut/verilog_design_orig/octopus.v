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

module octopus(
               //
               // Input Utopia interfaces x 8
               //
               Rx_clk_0,   Rx_clk_1,   Rx_clk_2,   Rx_clk_3,
               Rx_data_0,  Rx_data_1,  Rx_data_2,  Rx_data_3,
               Rx_soc_0,   Rx_soc_1,   Rx_soc_2,   Rx_soc_3, 
               Rx_en_0,    Rx_en_1,    Rx_en_2,    Rx_en_3,  
               Rx_empty_0, Rx_empty_1, Rx_empty_2, Rx_empty_3,
               
               Rx_clk_4,   Rx_clk_5,   Rx_clk_6,   Rx_clk_7,
               Rx_data_4,  Rx_data_5,  Rx_data_6,  Rx_data_7,
               Rx_soc_4,   Rx_soc_5,   Rx_soc_6,   Rx_soc_7, 
               Rx_en_4,    Rx_en_5,    Rx_en_6,    Rx_en_7,  
               Rx_empty_4, Rx_empty_5, Rx_empty_6, Rx_empty_7,

               //
               // Output Utopia interfaces x 8
               //
               Tx_clk_0,   Tx_clk_1,   Tx_clk_2,   Tx_clk_3,
               Tx_data_0,  Tx_data_1,  Tx_data_2,  Tx_data_3,
               Tx_soc_0,   Tx_soc_1,   Tx_soc_2,   Tx_soc_3, 
               Tx_en_0,    Tx_en_1,    Tx_en_2,    Tx_en_3,  
               Tx_full_0,  Tx_full_1,  Tx_full_2,  Tx_full_3,
               
               Tx_clk_4,   Tx_clk_5,   Tx_clk_6,   Tx_clk_7,
               Tx_data_4,  Tx_data_5,  Tx_data_6,  Tx_data_7,
               Tx_soc_4,   Tx_soc_5,   Tx_soc_6,   Tx_soc_7, 
               Tx_en_4,    Tx_en_5,    Tx_en_6,    Tx_en_7,  
               Tx_full_4,  Tx_full_5,  Tx_full_6,  Tx_full_7,

               //
               // Miscellaneous pins
               //
               clk,
               rst);

//
// Input Utopia interfaces x 8
//
output       Rx_clk_0,   Rx_clk_1,   Rx_clk_2,   Rx_clk_3;
input  [7:0] Rx_data_0,  Rx_data_1,  Rx_data_2,  Rx_data_3;
input        Rx_soc_0,   Rx_soc_1,   Rx_soc_2,   Rx_soc_3; 
output       Rx_en_0,    Rx_en_1,    Rx_en_2,    Rx_en_3;  
input        Rx_empty_0, Rx_empty_1, Rx_empty_2, Rx_empty_3;

output       Rx_clk_4,   Rx_clk_5,   Rx_clk_6,   Rx_clk_7;
input  [7:0] Rx_data_4,  Rx_data_5,  Rx_data_6,  Rx_data_7;
input        Rx_soc_4,   Rx_soc_5,   Rx_soc_6,   Rx_soc_7; 
output       Rx_en_4,    Rx_en_5,    Rx_en_6,    Rx_en_7;  
input        Rx_empty_4, Rx_empty_5, Rx_empty_6, Rx_empty_7;

//
// Output Utopia interfaces x 8
//
output       Tx_clk_0,   Tx_clk_1,   Tx_clk_2,   Tx_clk_3;
output [7:0] Tx_data_0,  Tx_data_1,  Tx_data_2,  Tx_data_3;
output       Tx_soc_0,   Tx_soc_1,   Tx_soc_2,   Tx_soc_3; 
output       Tx_en_0,    Tx_en_1,    Tx_en_2,    Tx_en_3;  
input        Tx_full_0,  Tx_full_1,  Tx_full_2,  Tx_full_3;

output       Tx_clk_4,   Tx_clk_5,   Tx_clk_6,   Tx_clk_7;
output [7:0] Tx_data_4,  Tx_data_5,  Tx_data_6,  Tx_data_7;
output       Tx_soc_4,   Tx_soc_5,   Tx_soc_6,   Tx_soc_7; 
output       Tx_en_4,    Tx_en_5,    Tx_en_6,    Tx_en_7;  
input        Tx_full_4,  Tx_full_5,  Tx_full_6,  Tx_full_7;

//
// Miscellaneous pins
//
input clk;
input rst;

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
      atm_rx_0.reset;
      atm_tx_0.reset;
      disable input_port_0;
      atm_rx_1.reset;
      atm_tx_1.reset;
      disable input_port_1;
      atm_rx_2.reset;
      atm_tx_2.reset;
      disable input_port_2;
      atm_rx_3.reset;
      atm_tx_3.reset;
      disable input_port_3;
      atm_rx_4.reset;
      atm_tx_4.reset;
      disable input_port_4;
      atm_rx_5.reset;
      atm_tx_5.reset;
      disable input_port_5;
      atm_rx_6.reset;
      atm_tx_6.reset;
      disable input_port_6;
      atm_rx_7.reset;
      atm_tx_7.reset;
      disable input_port_7;
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
   sc_mask = sc_mem[sc_vpi];

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
   sc_mem[sc_vpi] = sc_mask;
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
 
   qos_in_use = 1'b0;
end
endtask

//
// ATM-layer Utopia interface receivers
//
   
   utopia_atm_rx atm_rx_0(.clk   (Rx_clk_0),
                           .data  (Rx_data_0),
                           .soc   (Rx_soc_0),
                           .en    (Rx_en_0),
                           .empty (Rx_empty_0));

   
   utopia_atm_rx atm_rx_1(.clk   (Rx_clk_1),
                           .data  (Rx_data_1),
                           .soc   (Rx_soc_1),
                           .en    (Rx_en_1),
                           .empty (Rx_empty_1));

   
   utopia_atm_rx atm_rx_2(.clk   (Rx_clk_2),
                           .data  (Rx_data_2),
                           .soc   (Rx_soc_2),
                           .en    (Rx_en_2),
                           .empty (Rx_empty_2));

   
   utopia_atm_rx atm_rx_3(.clk   (Rx_clk_3),
                           .data  (Rx_data_3),
                           .soc   (Rx_soc_3),
                           .en    (Rx_en_3),
                           .empty (Rx_empty_3));

   
   utopia_atm_rx atm_rx_4(.clk   (Rx_clk_4),
                           .data  (Rx_data_4),
                           .soc   (Rx_soc_4),
                           .en    (Rx_en_4),
                           .empty (Rx_empty_4));

   
   utopia_atm_rx atm_rx_5(.clk   (Rx_clk_5),
                           .data  (Rx_data_5),
                           .soc   (Rx_soc_5),
                           .en    (Rx_en_5),
                           .empty (Rx_empty_5));

   
   utopia_atm_rx atm_rx_6(.clk   (Rx_clk_6),
                           .data  (Rx_data_6),
                           .soc   (Rx_soc_6),
                           .en    (Rx_en_6),
                           .empty (Rx_empty_6));

   
   utopia_atm_rx atm_rx_7(.clk   (Rx_clk_7),
                           .data  (Rx_data_7),
                           .soc   (Rx_soc_7),
                           .en    (Rx_en_7),
                           .empty (Rx_empty_7));


                       
//
// ATM-layer Utopia interface transmitters
//


   utopia_atm_tx atm_tx_0(.clk   (Tx_clk_0),
                           .data  (Tx_data_0),
                           .soc   (Tx_soc_0),
                           .en    (Tx_en_0),
                           .full  (Tx_full_0));

   utopia_atm_tx atm_tx_1(.clk   (Tx_clk_1),
                           .data  (Tx_data_1),
                           .soc   (Tx_soc_1),
                           .en    (Tx_en_1),
                           .full  (Tx_full_1));

   utopia_atm_tx atm_tx_2(.clk   (Tx_clk_2),
                           .data  (Tx_data_2),
                           .soc   (Tx_soc_2),
                           .en    (Tx_en_2),
                           .full  (Tx_full_2));

   utopia_atm_tx atm_tx_3(.clk   (Tx_clk_3),
                           .data  (Tx_data_3),
                           .soc   (Tx_soc_3),
                           .en    (Tx_en_3),
                           .full  (Tx_full_3));

   utopia_atm_tx atm_tx_4(.clk   (Tx_clk_4),
                           .data  (Tx_data_4),
                           .soc   (Tx_soc_4),
                           .en    (Tx_en_4),
                           .full  (Tx_full_4));

   utopia_atm_tx atm_tx_5(.clk   (Tx_clk_5),
                           .data  (Tx_data_5),
                           .soc   (Tx_soc_5),
                           .en    (Tx_en_5),
                           .full  (Tx_full_5));

   utopia_atm_tx atm_tx_6(.clk   (Tx_clk_6),
                           .data  (Tx_data_6),
                           .soc   (Tx_soc_6),
                           .en    (Tx_en_6),
                           .full  (Tx_full_6));

   utopia_atm_tx atm_tx_7(.clk   (Tx_clk_7),
                           .data  (Tx_data_7),
                           .soc   (Tx_soc_7),
                           .en    (Tx_en_7),
                           .full  (Tx_full_7));


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
// Switching logic
//

atm_cell atm_cell_0();
// These have to be at the module level
// to allow expression coverage by CoverMeter
reg [7:0] filter_0;
reg [7:0] cast_0;
always
begin: input_port_0
   reg [53*8:1] cell;
   reg          valid;

   `ifdef BADRI
   //if ($time == 0) begin
    #1;
   //end
   `endif

   atm_rx_0.get_cell(atm_rx_0.BLOCKING, cell, valid);
   // This should never happen in BLOCKING mode
   if (valid !== 1'b1) begin
      $write("ERROR: %M: Rx'ed cell on port #0 is not valid\n");
      disable input_port_0;
   end
   atm_cell_0.from_bits(cell);

   // If the HEC is bad, drop the cell
   if (!atm_cell_0.check_hec(0)) begin
      disable input_port_0;
   end

   //
   // Mutually exclusive region
   //

   begin: region
      request[0] = 1'b1;
      fork: wait4
         wait (owner === 0) disable wait4;
         begin
            repeat (1000) @ (posedge clk);
            $write("%M: Cannot obtain memory interface\n");
            $finish;
         end
      join
      
      // Get the switching information for this cell's VPI
      sc_read(atm_cell_0.vpi, {filter_0, cast_0});
      
      // Is this cell filtered out?
      if (filter_0[0]) begin
         disable region;
      end
      
      // Forward this cell to the appropriate
      // output ports
      if (cast_0[0]) begin
         atm_tx_0.put_cell(atm_tx_0.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_0
            reg [15:0] count;

            qos_read(atm_cell_0.vpi, count);
            count = count + 1;
            qos_write(atm_cell_0.vpi, count);
         end
      end
      if (cast_0[1]) begin
         atm_tx_1.put_cell(atm_tx_1.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_1
            reg [15:0] count;

            qos_read(atm_cell_0.vpi, count);
            count = count + 1;
            qos_write(atm_cell_0.vpi, count);
         end
      end
      if (cast_0[2]) begin
         atm_tx_2.put_cell(atm_tx_2.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_2
            reg [15:0] count;

            qos_read(atm_cell_0.vpi, count);
            count = count + 1;
            qos_write(atm_cell_0.vpi, count);
         end
      end
      if (cast_0[3]) begin
         atm_tx_3.put_cell(atm_tx_3.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_3
            reg [15:0] count;

            qos_read(atm_cell_0.vpi, count);
            count = count + 1;
            qos_write(atm_cell_0.vpi, count);
         end
      end
      if (cast_0[4]) begin
         atm_tx_4.put_cell(atm_tx_4.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_4
            reg [15:0] count;

            qos_read(atm_cell_0.vpi, count);
            count = count + 1;
            qos_write(atm_cell_0.vpi, count);
         end
      end
      if (cast_0[5]) begin
         atm_tx_5.put_cell(atm_tx_5.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_5
            reg [15:0] count;

            qos_read(atm_cell_0.vpi, count);
            count = count + 1;
            qos_write(atm_cell_0.vpi, count);
         end
      end
      if (cast_0[6]) begin
         atm_tx_6.put_cell(atm_tx_6.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_6
            reg [15:0] count;

            qos_read(atm_cell_0.vpi, count);
            count = count + 1;
            qos_write(atm_cell_0.vpi, count);
         end
      end
      if (cast_0[7]) begin
         atm_tx_7.put_cell(atm_tx_7.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_7
            reg [15:0] count;

            qos_read(atm_cell_0.vpi, count);
            count = count + 1;
            qos_write(atm_cell_0.vpi, count);
         end
      end
   end

   //
   // End of mutually exclusive region
   //
   request[0] = 1'b0;
   wait (owner !== 0);
end


atm_cell atm_cell_1();
// These have to be at the module level
// to allow expression coverage by CoverMeter
reg [7:0] filter_1;
reg [7:0] cast_1;
always
begin: input_port_1
   reg [53*8:1] cell;
   reg          valid;

   `ifdef BADRI
   //if ($time == 0) begin
    #1;
   //end
   `endif
   

   atm_rx_1.get_cell(atm_rx_1.BLOCKING, cell, valid);
   // This should never happen in BLOCKING mode
   if (valid !== 1'b1) begin
      $write("ERROR: %M: Rx'ed cell on port #1 is not valid\n");
      disable input_port_1;
   end
   atm_cell_1.from_bits(cell);

   // If the HEC is bad, drop the cell
   if (!atm_cell_1.check_hec(0)) begin
      disable input_port_1;
   end

   //
   // Mutually exclusive region
   //

   begin: region
      request[1] = 1'b1;
      fork: wait4
         wait (owner === 1) disable wait4;
         begin
            repeat (1000) @ (posedge clk);
            $write("%M: Cannot obtain memory interface\n");
            $finish;
         end
      join
      
      // Get the switching information for this cell's VPI
      sc_read(atm_cell_1.vpi, {filter_1, cast_1});
      
      // Is this cell filtered out?
      if (filter_1[1]) begin
         disable region;
      end
      
      // Forward this cell to the appropriate
      // output ports
      if (cast_1[0]) begin
         atm_tx_0.put_cell(atm_tx_0.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_0
            reg [15:0] count;

            qos_read(atm_cell_1.vpi, count);
            count = count + 1;
            qos_write(atm_cell_1.vpi, count);
         end
      end
      if (cast_1[1]) begin
         atm_tx_1.put_cell(atm_tx_1.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_1
            reg [15:0] count;

            qos_read(atm_cell_1.vpi, count);
            count = count + 1;
            qos_write(atm_cell_1.vpi, count);
         end
      end
      if (cast_1[2]) begin
         atm_tx_2.put_cell(atm_tx_2.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_2
            reg [15:0] count;

            qos_read(atm_cell_1.vpi, count);
            count = count + 1;
            qos_write(atm_cell_1.vpi, count);
         end
      end
      if (cast_1[3]) begin
         atm_tx_3.put_cell(atm_tx_3.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_3
            reg [15:0] count;

            qos_read(atm_cell_1.vpi, count);
            count = count + 1;
            qos_write(atm_cell_1.vpi, count);
         end
      end
      if (cast_1[4]) begin
         atm_tx_4.put_cell(atm_tx_4.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_4
            reg [15:0] count;

            qos_read(atm_cell_1.vpi, count);
            count = count + 1;
            qos_write(atm_cell_1.vpi, count);
         end
      end
      if (cast_1[5]) begin
         atm_tx_5.put_cell(atm_tx_5.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_5
            reg [15:0] count;

            qos_read(atm_cell_1.vpi, count);
            count = count + 1;
            qos_write(atm_cell_1.vpi, count);
         end
      end
      if (cast_1[6]) begin
         atm_tx_6.put_cell(atm_tx_6.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_6
            reg [15:0] count;

            qos_read(atm_cell_1.vpi, count);
            count = count + 1;
            qos_write(atm_cell_1.vpi, count);
         end
      end
      if (cast_1[7]) begin
         atm_tx_7.put_cell(atm_tx_7.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_7
            reg [15:0] count;

            qos_read(atm_cell_1.vpi, count);
            count = count + 1;
            qos_write(atm_cell_1.vpi, count);
         end
      end
   end

   //
   // End of mutually exclusive region
   //
   request[1] = 1'b0;
   wait (owner !== 1);
end


atm_cell atm_cell_2();
// These have to be at the module level
// to allow expression coverage by CoverMeter
reg [7:0] filter_2;
reg [7:0] cast_2;
always
begin: input_port_2
   reg [53*8:1] cell;
   reg          valid;

   `ifdef BADRI
   //if ($time == 0) begin
    #1;
   //end
   `endif

   atm_rx_2.get_cell(atm_rx_2.BLOCKING, cell, valid);
   // This should never happen in BLOCKING mode
   if (valid !== 1'b1) begin
      $write("ERROR: %M: Rx'ed cell on port #2 is not valid\n");
      disable input_port_2;
   end
   atm_cell_2.from_bits(cell);

   // If the HEC is bad, drop the cell
   if (!atm_cell_2.check_hec(0)) begin
      disable input_port_2;
   end

   //
   // Mutually exclusive region
   //

   begin: region
      request[2] = 1'b1;
      fork: wait4
         wait (owner === 2) disable wait4;
         begin
            repeat (1000) @ (posedge clk);
            $write("%M: Cannot obtain memory interface\n");
            $finish;
         end
      join
      
      // Get the switching information for this cell's VPI
      sc_read(atm_cell_2.vpi, {filter_2, cast_2});
      
      // Is this cell filtered out?
      if (filter_2[2]) begin
         disable region;
      end
      
      // Forward this cell to the appropriate
      // output ports
      if (cast_2[0]) begin
         atm_tx_0.put_cell(atm_tx_0.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_0
            reg [15:0] count;

            qos_read(atm_cell_2.vpi, count);
            count = count + 1;
            qos_write(atm_cell_2.vpi, count);
         end
      end
      if (cast_2[1]) begin
         atm_tx_1.put_cell(atm_tx_1.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_1
            reg [15:0] count;

            qos_read(atm_cell_2.vpi, count);
            count = count + 1;
            qos_write(atm_cell_2.vpi, count);
         end
      end
      if (cast_2[2]) begin
         atm_tx_2.put_cell(atm_tx_2.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_2
            reg [15:0] count;

            qos_read(atm_cell_2.vpi, count);
            count = count + 1;
            qos_write(atm_cell_2.vpi, count);
         end
      end
      if (cast_2[3]) begin
         atm_tx_3.put_cell(atm_tx_3.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_3
            reg [15:0] count;

            qos_read(atm_cell_2.vpi, count);
            count = count + 1;
            qos_write(atm_cell_2.vpi, count);
         end
      end
      if (cast_2[4]) begin
         atm_tx_4.put_cell(atm_tx_4.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_4
            reg [15:0] count;

            qos_read(atm_cell_2.vpi, count);
            count = count + 1;
            qos_write(atm_cell_2.vpi, count);
         end
      end
      if (cast_2[5]) begin
         atm_tx_5.put_cell(atm_tx_5.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_5
            reg [15:0] count;

            qos_read(atm_cell_2.vpi, count);
            count = count + 1;
            qos_write(atm_cell_2.vpi, count);
         end
      end
      if (cast_2[6]) begin
         atm_tx_6.put_cell(atm_tx_6.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_6
            reg [15:0] count;

            qos_read(atm_cell_2.vpi, count);
            count = count + 1;
            qos_write(atm_cell_2.vpi, count);
         end
      end
      if (cast_2[7]) begin
         atm_tx_7.put_cell(atm_tx_7.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_7
            reg [15:0] count;

            qos_read(atm_cell_2.vpi, count);
            count = count + 1;
            qos_write(atm_cell_2.vpi, count);
         end
      end
   end

   //
   // End of mutually exclusive region
   //
   request[2] = 1'b0;
   wait (owner !== 2);
end


atm_cell atm_cell_3();
// These have to be at the module level
// to allow expression coverage by CoverMeter
reg [7:0] filter_3;
reg [7:0] cast_3;
always
begin: input_port_3
   reg [53*8:1] cell;
   reg          valid;
   `ifdef BADRI
   //if ($time == 0) begin
    #1;
   //end
   `endif

   atm_rx_3.get_cell(atm_rx_3.BLOCKING, cell, valid);
   // This should never happen in BLOCKING mode
   if (valid !== 1'b1) begin
      $write("ERROR: %M: Rx'ed cell on port #3 is not valid\n");
      disable input_port_3;
   end
   atm_cell_3.from_bits(cell);

   // If the HEC is bad, drop the cell
   if (!atm_cell_3.check_hec(0)) begin
      disable input_port_3;
   end

   //
   // Mutually exclusive region
   //

   begin: region
      request[3] = 1'b1;
      fork: wait4
         wait (owner === 3) disable wait4;
         begin
            repeat (1000) @ (posedge clk);
            $write("%M: Cannot obtain memory interface\n");
            $finish;
         end
      join
      
      // Get the switching information for this cell's VPI
      sc_read(atm_cell_3.vpi, {filter_3, cast_3});
      
      // Is this cell filtered out?
      if (filter_3[3]) begin
         disable region;
      end
      
      // Forward this cell to the appropriate
      // output ports
      if (cast_3[0]) begin
         atm_tx_0.put_cell(atm_tx_0.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_0
            reg [15:0] count;

            qos_read(atm_cell_3.vpi, count);
            count = count + 1;
            qos_write(atm_cell_3.vpi, count);
         end
      end
      if (cast_3[1]) begin
         atm_tx_1.put_cell(atm_tx_1.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_1
            reg [15:0] count;

            qos_read(atm_cell_3.vpi, count);
            count = count + 1;
            qos_write(atm_cell_3.vpi, count);
         end
      end
      if (cast_3[2]) begin
         atm_tx_2.put_cell(atm_tx_2.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_2
            reg [15:0] count;

            qos_read(atm_cell_3.vpi, count);
            count = count + 1;
            qos_write(atm_cell_3.vpi, count);
         end
      end
      if (cast_3[3]) begin
         atm_tx_3.put_cell(atm_tx_3.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_3
            reg [15:0] count;

            qos_read(atm_cell_3.vpi, count);
            count = count + 1;
            qos_write(atm_cell_3.vpi, count);
         end
      end
      if (cast_3[4]) begin
         atm_tx_4.put_cell(atm_tx_4.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_4
            reg [15:0] count;

            qos_read(atm_cell_3.vpi, count);
            count = count + 1;
            qos_write(atm_cell_3.vpi, count);
         end
      end
      if (cast_3[5]) begin
         atm_tx_5.put_cell(atm_tx_5.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_5
            reg [15:0] count;

            qos_read(atm_cell_3.vpi, count);
            count = count + 1;
            qos_write(atm_cell_3.vpi, count);
         end
      end
      if (cast_3[6]) begin
         atm_tx_6.put_cell(atm_tx_6.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_6
            reg [15:0] count;

            qos_read(atm_cell_3.vpi, count);
            count = count + 1;
            qos_write(atm_cell_3.vpi, count);
         end
      end
      if (cast_3[7]) begin
         atm_tx_7.put_cell(atm_tx_7.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_7
            reg [15:0] count;

            qos_read(atm_cell_3.vpi, count);
            count = count + 1;
            qos_write(atm_cell_3.vpi, count);
         end
      end
   end

   //
   // End of mutually exclusive region
   //
   request[3] = 1'b0;
   wait (owner !== 3);
end


atm_cell atm_cell_4();
// These have to be at the module level
// to allow expression coverage by CoverMeter
reg [7:0] filter_4;
reg [7:0] cast_4;
always
begin: input_port_4
   reg [53*8:1] cell;
   reg          valid;
   `ifdef BADRI
   //if ($time == 0) begin
    #1;
   //end
   `endif

   atm_rx_4.get_cell(atm_rx_4.BLOCKING, cell, valid);
   // This should never happen in BLOCKING mode
   if (valid !== 1'b1) begin
      $write("ERROR: %M: Rx'ed cell on port #4 is not valid\n");
      disable input_port_4;
   end
   atm_cell_4.from_bits(cell);

   // If the HEC is bad, drop the cell
   if (!atm_cell_4.check_hec(0)) begin
      disable input_port_4;
   end

   //
   // Mutually exclusive region
   //

   begin: region
      request[4] = 1'b1;
      fork: wait4
         wait (owner === 4) disable wait4;
         begin
            repeat (1000) @ (posedge clk);
            $write("%M: Cannot obtain memory interface\n");
            $finish;
         end
      join
      
      // Get the switching information for this cell's VPI
      sc_read(atm_cell_4.vpi, {filter_4, cast_4});
      
      // Is this cell filtered out?
      if (filter_4[4]) begin
         disable region;
      end
      
      // Forward this cell to the appropriate
      // output ports
      if (cast_4[0]) begin
         atm_tx_0.put_cell(atm_tx_0.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_0
            reg [15:0] count;

            qos_read(atm_cell_4.vpi, count);
            count = count + 1;
            qos_write(atm_cell_4.vpi, count);
         end
      end
      if (cast_4[1]) begin
         atm_tx_1.put_cell(atm_tx_1.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_1
            reg [15:0] count;

            qos_read(atm_cell_4.vpi, count);
            count = count + 1;
            qos_write(atm_cell_4.vpi, count);
         end
      end
      if (cast_4[2]) begin
         atm_tx_2.put_cell(atm_tx_2.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_2
            reg [15:0] count;

            qos_read(atm_cell_4.vpi, count);
            count = count + 1;
            qos_write(atm_cell_4.vpi, count);
         end
      end
      if (cast_4[3]) begin
         atm_tx_3.put_cell(atm_tx_3.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_3
            reg [15:0] count;

            qos_read(atm_cell_4.vpi, count);
            count = count + 1;
            qos_write(atm_cell_4.vpi, count);
         end
      end
      if (cast_4[4]) begin
         atm_tx_4.put_cell(atm_tx_4.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_4
            reg [15:0] count;

            qos_read(atm_cell_4.vpi, count);
            count = count + 1;
            qos_write(atm_cell_4.vpi, count);
         end
      end
      if (cast_4[5]) begin
         atm_tx_5.put_cell(atm_tx_5.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_5
            reg [15:0] count;

            qos_read(atm_cell_4.vpi, count);
            count = count + 1;
            qos_write(atm_cell_4.vpi, count);
         end
      end
      if (cast_4[6]) begin
         atm_tx_6.put_cell(atm_tx_6.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_6
            reg [15:0] count;

            qos_read(atm_cell_4.vpi, count);
            count = count + 1;
            qos_write(atm_cell_4.vpi, count);
         end
      end
      if (cast_4[7]) begin
         atm_tx_7.put_cell(atm_tx_7.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_7
            reg [15:0] count;

            qos_read(atm_cell_4.vpi, count);
            count = count + 1;
            qos_write(atm_cell_4.vpi, count);
         end
      end
   end

   //
   // End of mutually exclusive region
   //
   request[4] = 1'b0;
   wait (owner !== 4);
end


atm_cell atm_cell_5();
// These have to be at the module level
// to allow expression coverage by CoverMeter
reg [7:0] filter_5;
reg [7:0] cast_5;
always
begin: input_port_5
   reg [53*8:1] cell;
   reg          valid;
   `ifdef BADRI
   //if ($time == 0) begin
    #1;
   //end
   `endif

   atm_rx_5.get_cell(atm_rx_5.BLOCKING, cell, valid);
   // This should never happen in BLOCKING mode
   if (valid !== 1'b1) begin
      $write("ERROR: %M: Rx'ed cell on port #5 is not valid\n");
      disable input_port_5;
   end
   atm_cell_5.from_bits(cell);

   // If the HEC is bad, drop the cell
   if (!atm_cell_5.check_hec(0)) begin
      disable input_port_5;
   end

   //
   // Mutually exclusive region
   //

   begin: region
      request[5] = 1'b1;
      fork: wait4
         wait (owner === 5) disable wait4;
         begin
            repeat (1000) @ (posedge clk);
            $write("%M: Cannot obtain memory interface\n");
            $finish;
         end
      join
      
      // Get the switching information for this cell's VPI
      sc_read(atm_cell_5.vpi, {filter_5, cast_5});
      
      // Is this cell filtered out?
      if (filter_5[5]) begin
         disable region;
      end
      
      // Forward this cell to the appropriate
      // output ports
      if (cast_5[0]) begin
         atm_tx_0.put_cell(atm_tx_0.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_0
            reg [15:0] count;

            qos_read(atm_cell_5.vpi, count);
            count = count + 1;
            qos_write(atm_cell_5.vpi, count);
         end
      end
      if (cast_5[1]) begin
         atm_tx_1.put_cell(atm_tx_1.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_1
            reg [15:0] count;

            qos_read(atm_cell_5.vpi, count);
            count = count + 1;
            qos_write(atm_cell_5.vpi, count);
         end
      end
      if (cast_5[2]) begin
         atm_tx_2.put_cell(atm_tx_2.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_2
            reg [15:0] count;

            qos_read(atm_cell_5.vpi, count);
            count = count + 1;
            qos_write(atm_cell_5.vpi, count);
         end
      end
      if (cast_5[3]) begin
         atm_tx_3.put_cell(atm_tx_3.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_3
            reg [15:0] count;

            qos_read(atm_cell_5.vpi, count);
            count = count + 1;
            qos_write(atm_cell_5.vpi, count);
         end
      end
      if (cast_5[4]) begin
         atm_tx_4.put_cell(atm_tx_4.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_4
            reg [15:0] count;

            qos_read(atm_cell_5.vpi, count);
            count = count + 1;
            qos_write(atm_cell_5.vpi, count);
         end
      end
      if (cast_5[5]) begin
         atm_tx_5.put_cell(atm_tx_5.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_5
            reg [15:0] count;

            qos_read(atm_cell_5.vpi, count);
            count = count + 1;
            qos_write(atm_cell_5.vpi, count);
         end
      end
      if (cast_5[6]) begin
         atm_tx_6.put_cell(atm_tx_6.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_6
            reg [15:0] count;

            qos_read(atm_cell_5.vpi, count);
            count = count + 1;
            qos_write(atm_cell_5.vpi, count);
         end
      end
      if (cast_5[7]) begin
         atm_tx_7.put_cell(atm_tx_7.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_7
            reg [15:0] count;

            qos_read(atm_cell_5.vpi, count);
            count = count + 1;
            qos_write(atm_cell_5.vpi, count);
         end
      end
   end

   //
   // End of mutually exclusive region
   //
   request[5] = 1'b0;
   wait (owner !== 5);
end


atm_cell atm_cell_6();
// These have to be at the module level
// to allow expression coverage by CoverMeter
reg [7:0] filter_6;
reg [7:0] cast_6;
always
begin: input_port_6
   reg [53*8:1] cell;
   reg          valid;
   `ifdef BADRI
   //if ($time == 0) begin
    #1;
   //end
   `endif

   atm_rx_6.get_cell(atm_rx_6.BLOCKING, cell, valid);
   // This should never happen in BLOCKING mode
   if (valid !== 1'b1) begin
      $write("ERROR: %M: Rx'ed cell on port #6 is not valid\n");
      disable input_port_6;
   end
   atm_cell_6.from_bits(cell);

   // If the HEC is bad, drop the cell
   if (!atm_cell_6.check_hec(0)) begin
      disable input_port_6;
   end

   //
   // Mutually exclusive region
   //

   begin: region
      request[6] = 1'b1;
      fork: wait4
         wait (owner === 6) disable wait4;
         begin
            repeat (1000) @ (posedge clk);
            $write("%M: Cannot obtain memory interface\n");
            $finish;
         end
      join
      
      // Get the switching information for this cell's VPI
      sc_read(atm_cell_6.vpi, {filter_6, cast_6});
      
      // Is this cell filtered out?
      if (filter_6[6]) begin
         disable region;
      end
      
      // Forward this cell to the appropriate
      // output ports
      if (cast_6[0]) begin
         atm_tx_0.put_cell(atm_tx_0.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_0
            reg [15:0] count;

            qos_read(atm_cell_6.vpi, count);
            count = count + 1;
            qos_write(atm_cell_6.vpi, count);
         end
      end
      if (cast_6[1]) begin
         atm_tx_1.put_cell(atm_tx_1.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_1
            reg [15:0] count;

            qos_read(atm_cell_6.vpi, count);
            count = count + 1;
            qos_write(atm_cell_6.vpi, count);
         end
      end
      if (cast_6[2]) begin
         atm_tx_2.put_cell(atm_tx_2.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_2
            reg [15:0] count;

            qos_read(atm_cell_6.vpi, count);
            count = count + 1;
            qos_write(atm_cell_6.vpi, count);
         end
      end
      if (cast_6[3]) begin
         atm_tx_3.put_cell(atm_tx_3.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_3
            reg [15:0] count;

            qos_read(atm_cell_6.vpi, count);
            count = count + 1;
            qos_write(atm_cell_6.vpi, count);
         end
      end
      if (cast_6[4]) begin
         atm_tx_4.put_cell(atm_tx_4.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_4
            reg [15:0] count;

            qos_read(atm_cell_6.vpi, count);
            count = count + 1;
            qos_write(atm_cell_6.vpi, count);
         end
      end
      if (cast_6[5]) begin
         atm_tx_5.put_cell(atm_tx_5.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_5
            reg [15:0] count;

            qos_read(atm_cell_6.vpi, count);
            count = count + 1;
            qos_write(atm_cell_6.vpi, count);
         end
      end
      if (cast_6[6]) begin
         atm_tx_6.put_cell(atm_tx_6.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_6
            reg [15:0] count;

            qos_read(atm_cell_6.vpi, count);
            count = count + 1;
            qos_write(atm_cell_6.vpi, count);
         end
      end
      if (cast_6[7]) begin
         atm_tx_7.put_cell(atm_tx_7.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_7
            reg [15:0] count;

            qos_read(atm_cell_6.vpi, count);
            count = count + 1;
            qos_write(atm_cell_6.vpi, count);
         end
      end
   end

   //
   // End of mutually exclusive region
   //
   request[6] = 1'b0;
   wait (owner !== 6);
end


atm_cell atm_cell_7();
// These have to be at the module level
// to allow expression coverage by CoverMeter
reg [7:0] filter_7;
reg [7:0] cast_7;
always
begin: input_port_7
   reg [53*8:1] cell;
   reg          valid;
   `ifdef BADRI
   //if ($time == 0) begin
    #1;
   //end
   `endif

   atm_rx_7.get_cell(atm_rx_7.BLOCKING, cell, valid);
   // This should never happen in BLOCKING mode
   if (valid !== 1'b1) begin
      $write("ERROR: %M: Rx'ed cell on port #7 is not valid\n");
      disable input_port_7;
   end
   atm_cell_7.from_bits(cell);

   // If the HEC is bad, drop the cell
   if (!atm_cell_7.check_hec(0)) begin
      disable input_port_7;
   end

   //
   // Mutually exclusive region
   //

   begin: region
      request[7] = 1'b1;
      fork: wait4
         wait (owner === 7) disable wait4;
         begin
            repeat (1000) @ (posedge clk);
            $write("%M: Cannot obtain memory interface\n");
            $finish;
         end
      join
      
      // Get the switching information for this cell's VPI
      sc_read(atm_cell_7.vpi, {filter_7, cast_7});
      
      // Is this cell filtered out?
      if (filter_7[7]) begin
         disable region;
      end
      
      // Forward this cell to the appropriate
      // output ports
      if (cast_7[0]) begin
         atm_tx_0.put_cell(atm_tx_0.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_0
            reg [15:0] count;

            qos_read(atm_cell_7.vpi, count);
            count = count + 1;
            qos_write(atm_cell_7.vpi, count);
         end
      end
      if (cast_7[1]) begin
         atm_tx_1.put_cell(atm_tx_1.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_1
            reg [15:0] count;

            qos_read(atm_cell_7.vpi, count);
            count = count + 1;
            qos_write(atm_cell_7.vpi, count);
         end
      end
      if (cast_7[2]) begin
         atm_tx_2.put_cell(atm_tx_2.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_2
            reg [15:0] count;

            qos_read(atm_cell_7.vpi, count);
            count = count + 1;
            qos_write(atm_cell_7.vpi, count);
         end
      end
      if (cast_7[3]) begin
         atm_tx_3.put_cell(atm_tx_3.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_3
            reg [15:0] count;

            qos_read(atm_cell_7.vpi, count);
            count = count + 1;
            qos_write(atm_cell_7.vpi, count);
         end
      end
      if (cast_7[4]) begin
         atm_tx_4.put_cell(atm_tx_4.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_4
            reg [15:0] count;

            qos_read(atm_cell_7.vpi, count);
            count = count + 1;
            qos_write(atm_cell_7.vpi, count);
         end
      end
      if (cast_7[5]) begin
         atm_tx_5.put_cell(atm_tx_5.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_5
            reg [15:0] count;

            qos_read(atm_cell_7.vpi, count);
            count = count + 1;
            qos_write(atm_cell_7.vpi, count);
         end
      end
      if (cast_7[6]) begin
         atm_tx_6.put_cell(atm_tx_6.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_6
            reg [15:0] count;

            qos_read(atm_cell_7.vpi, count);
            count = count + 1;
            qos_write(atm_cell_7.vpi, count);
         end
      end
      if (cast_7[7]) begin
         atm_tx_7.put_cell(atm_tx_7.NON_BLOCK,
                            cell, valid);
         // Was the cell dropped?
         if (valid !== 1'b1) begin: QoS_7
            reg [15:0] count;

            qos_read(atm_cell_7.vpi, count);
            count = count + 1;
            qos_write(atm_cell_7.vpi, count);
         end
      end
   end

   //
   // End of mutually exclusive region
   //
   request[7] = 1'b0;
   wait (owner !== 7);
end


endmodule

