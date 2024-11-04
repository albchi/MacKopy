module amp(input real in, output real out);
  parameter real gain = 1.0; 

  always @(in) begin
    out <= gain * in;
  end
endmodule
