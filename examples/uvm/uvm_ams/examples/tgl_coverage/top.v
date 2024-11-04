// Top cell with 5 chain inverters, but pushing
// thru one more level of hierarchy by my_buf

`timescale 1ns / 10ps

module test;
reg clk;
reg d2a_xmr;
wire l_a2d_xmr;
real r_a2d_xmr;
real s_a2d_xmr;
real pos_crossing_time, neg_crossing_time, pulse_width;

spi_blk i1 (.in(clk) );

initial begin
  clk = 0;
  forever begin
     if (clk==1'b0) begin
       s_a2d_xmr =  $snps_get_volt(test.i1.mon);
       #1 clk = 1'b1;
     end
     else
       #9 clk = 1'b0;
  end
end

initial begin
  $dumpvars();
  $dumpfile("digital_output.vcd");
  #200 
  pulse_width = neg_crossing_time - pos_crossing_time;
  $display("***********************************************");
  $display("** Pulse width for signal test.i1.mon: %g    **",pulse_width);
  $display("***********************************************");
  $finish();
end

/**** Logic XMR: Write operations ****/
initial begin 
#50 d2a_xmr = 1'b1;
#30 d2a_xmr = 1'b0;
#50 d2a_xmr = 1'b1;
#30 d2a_xmr = 1'b0;
end

assign test.i1.ctl = d2a_xmr;
assign l_a2d_xmr = test.i1.mon;
//assign r_a2d_xmr = test.i1.mon;

/**** Logic XMR: Read operations ****/
always @ (posedge l_a2d_xmr) begin 
  r_a2d_xmr =  $snps_get_volt(test.i1.mon);
  pos_crossing_time = $time;
end

always @ (negedge l_a2d_xmr ) begin
  neg_crossing_time = $time ;
  pulse_width = neg_crossing_time - pos_crossing_time;
  r_a2d_xmr =  $snps_get_volt(test.i1.mon);
end

endmodule

