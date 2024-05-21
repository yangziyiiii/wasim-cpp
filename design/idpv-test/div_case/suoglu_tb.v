`timescale 1ns / 1ps

module tb_divider;

  // Parameters
  parameter WIDTH = 32;
  parameter CACHING = 1;
  parameter INIT_VLD = 0;

  // Inputs
  reg clk;
  reg rst;
  reg start;
  reg [WIDTH-1:0] dividend;
  reg [WIDTH-1:0] divisor;

  // Outputs
  wire [WIDTH-1:0] quotient;
  wire [WIDTH-1:0] remainder;
  wire zeroErr;
  wire valid;

  // Instantiate the Unit Under Test (UUT)
  divider #(
    .WIDTH(WIDTH),
    .CACHING(CACHING),
    .INIT_VLD(INIT_VLD)
  ) uut (
    .clk(clk),
    .rst(rst),
    .start(start),
    .dividend(dividend),
    .divisor(divisor),
    .quotient(quotient),
    .remainder(remainder),
    .zeroErr(zeroErr),
    .valid(valid)
  );

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk; // 10ns period
  end

  // Stimulus
  initial begin
    // Initialize Inputs
    rst = 1;
    start = 0;
    dividend = 0;
    divisor = 0;
    $dumpfile("wave.vcd");
    $dumpvars(0, tb_divider); 


    // Wait for global reset
    #100;
    rst = 0;

    // Apply test cases
    // Test Case 1: Normal division
    dividend = 32'b00010000000000000000000000000001;
    divisor = 32'b00100000000000000000000000000001;
    start = 1;
    #10 start = 0;
    wait (valid);
    #200;


    // Finish simulation
    $finish;
  end

  // Monitor
  initial begin
    $monitor("Time=%0t, rst=%b, start=%b, dividend=%h, divisor=%h, quotient=%h, remainder=%h, zeroErr=%b, valid=%b", 
             $time, rst, start, dividend, divisor, quotient, remainder, zeroErr, valid);
  end

endmodule
