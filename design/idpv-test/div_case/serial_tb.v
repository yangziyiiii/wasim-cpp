`timescale 1ns / 1ps

module tb_serial_divide_uu;

// Parameters
parameter M_PP = 16;           // Size of dividend
parameter N_PP = 8;            // Size of divisor
parameter R_PP = 0;            // Size of remainder
parameter S_PP = 0;            // Skip this many bits (known leading zeros)
parameter COUNT_WIDTH_PP = 5;  // Count width

// Inputs
reg clk_i;
reg clk_en_i;
reg rst_i;
reg divide_i;
reg [M_PP-1:0] dividend_i;
reg [N_PP-1:0] divisor_i;

// Outputs
wire [M_PP+R_PP-S_PP-1:0] quotient_o;
wire done_o;

// Instantiate the Unit Under Test (UUT)
serial_divide_uu #(
    .M_PP(M_PP),
    .N_PP(N_PP),
    .R_PP(R_PP),
    .S_PP(S_PP),
    .COUNT_WIDTH_PP(COUNT_WIDTH_PP)
) uut (
    .clk_i(clk_i),
    .clk_en_i(clk_en_i),
    .rst_i(rst_i),
    .divide_i(divide_i),
    .dividend_i(dividend_i),
    .divisor_i(divisor_i),
    .quotient_o(quotient_o),
    .done_o(done_o)
);

// Clock generation
initial begin
    clk_i = 0;
    forever #10 clk_i = ~clk_i;  // 50 MHz clock
end

// Reset process
initial begin
    rst_i = 1;
    #100;
    rst_i = 0;
end

// Test cases
initial begin
    // Initialize inputs
    clk_en_i = 0;
    divide_i = 0;
    dividend_i = 0;
    divisor_i = 0;
    
    // Apply reset
    #150;
    
    // Enable clock
    clk_en_i = 1;
    
    // Test Case 1: Divide by zero
    #20;
    dividend_i = 16'd1234;
    divisor_i = 8'd0;
    divide_i = 1;
    #20;
    divide_i = 0;

    // Wait for completion
    wait(done_o == 1);
    $display("Test Case 1: Dividend = %d, Divisor = %d, Quotient = %d", dividend_i, divisor_i, quotient_o);
    
    // Test Case 2: Normal division
    #100;
    dividend_i = 16'd65535;
    divisor_i = 8'd255;
    divide_i = 1;
    #20;
    divide_i = 0;
    
    // Wait for completion
    wait(done_o == 1);
    $display("Test Case 2: Dividend = %d, Divisor = %d, Quotient = %d", dividend_i, divisor_i, quotient_o);

    // More tests can be added here

    // Finish the simulation
    #100;
    $finish;
end

endmodule
