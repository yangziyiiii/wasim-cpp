`timescale 1ns / 1ps

module tb_div_uu;

  // Parameters
  parameter z_width = 16;
  parameter d_width = z_width / 2;

  // Inputs
  reg clk;
  reg ena;
  reg [z_width-1:0] z;
  reg [d_width-1:0] d;

  // Outputs
  wire [d_width-1:0] q;
  wire [d_width-1:0] s;
  wire div0;
  wire ovf;

  // Instantiate the Unit Under Test (UUT)
  div_uu #(
    .z_width(z_width),
    .d_width(d_width)
  ) uut (
    .clk(clk),
    .ena(ena),
    .z(z),
    .d(d),
    .q(q),
    .s(s),
    .div0(div0),
    .ovf(ovf)
  );

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end


  // Stimulus
  initial begin
    // Initialize Inputs
    ena = 0;
    z = 0;
    d = 0;
    $dumpfile("wave.vcd");
    $dumpvars(0, tb_div_uu); 

    // Wait for global reset
    #100;

    // Apply test cases
    // Test Case 1: Normal division
    z = 16'b0000000001111111;  
    d = 8'b00000001; 
    ena = 1;
    #20;
    ena = 0;
    #100000;

    // Finish simulation
    $finish;
  end

  // Monitor
  initial begin
    $monitor("Time=%t, z=%d, d=%d, q=%d, s=%d", $time, z, d, q, s,);
  end

endmodule

