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
//      Type definition for an UNI ATM cell
//
// Author:      $Author: badri $
// Revision:    $Revision: 1.1 $
//

module atm_cell;

reg [ 3:0] gfc;
reg [ 7:0] vpi;
reg [15:0] vci;
reg [ 2:0] pt;
reg        clp;
reg [ 7:0] hec;
reg [ 7:0] payload [0:47];


//
// Symbolic values about what to do with the HEC
// field when packing into bits
// Also used for the 'compute_hec' function.
//
parameter
         GOOD_HEC  = 2'b00,
         BAD_HEC   = 2'b01,
         AS_IS_HEC = 2'b11;

//
// Function to compute a good or bad HEC value
//
function [7:0] compute_hec;
   input todo_hec;             // GOOD_HEC or BAD_HEC

   reg [4*8:1] hdr;
   integer i;
begin
   // Pack the header fields before computing the CRC
   hdr = {gfc, vpi, vci, pt, clp};

   // Compute the HEC
   compute_hec = {hdr, 8'h00} % 9'b100000111;
   compute_hec = compute_hec ^ 8'b01010101;

   // Optionally corrupt the HEC
   // by toggling a random bit
   if (todo_hec == BAD_HEC) begin
      compute_hec = compute_hec ^ (8'b1 << ($random % 8));
   end
end
endfunction


//
// Function to check the HEC value
//
function check_hec;
   input dummy;

   reg [7:0] ahec;
begin
   ahec = compute_hec(GOOD_HEC);
   check_hec = (compute_hec(GOOD_HEC) === hec);
end
endfunction


//
// Pack the ATM cell into an array of bits
//
function [53*8:1] to_bits;
   input [1:0] todo_hec;       // GOOD_HEC, BAD_HEC or AS_IS_HEC

   integer i;
begin
   // Deal with the HEC
   if (todo_hec !== AS_IS_HEC) begin
      // Compute a new HEC value
      hec = compute_hec(todo_hec[0]);
   end
   
   // Pack the header
   to_bits = {gfc, vpi, vci, pt, clp, hec};
   
   // Pack the payload
   for (i = 0; i < 48; i = i + 1) begin
      to_bits = to_bits << 8;
      to_bits[8:1] = payload[i];
   end
end
endfunction
          

//
// Unpack the ATM cell from an array of bits
//
task from_bits;
   input [53*8:1] bits;

   integer i;
begin
   // Unpack the payload
   for (i = 47; i >= 0; i = i - 1) begin
      payload[i] = bits[8:1];
      bits = bits >> 8;
   end
   // Unpack the header
   {gfc, vpi, vci, pt, clp, hec} = bits;
end
endtask


//
// Randomize the content of the cell
//
task randomize;
   input todo_hec;   // GOOD_HEC or BAD_HEC;

   integer i;
begin
   gfc = $random;
   vpi = $random;
   vci = $random;
   pt  = $random;
   clp = $random;
   hec = compute_hec(todo_hec);

   for (i = 0; i < 48; i = i + 1) begin
      payload[i] = $random;
   end
end
endtask


//
// Display the content of the cell
//
task display;
   integer i;
begin
   $write("   GFC =  4'b%b\n", gfc);
   $write("   VPI =  8'h%h\n", vpi);
   $write("   VCI = 16'h%h\n", vci);
   $write("   PT  =  3'b%b\n", pt);
   $write("   CLP =  1'b%b\n", clp);
   $write("   HEC =  8'h%h (%0s)\n",
          hec, (check_hec(0)) ? "good" : "BAD");

   $write("   PAY =");
   for (i = 0; i < 48; i = i + 1) begin
      if ((i % 8) == 0 && i != 0) $write("\n        ");
      $write(" %h", payload[i]);
   end
   $write("\n");
end
endtask
          
endmodule
