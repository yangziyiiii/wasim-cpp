`timescale 1ns / 1ps

module encryptor_top_tb;

    // Inputs
    reg clk1;
    reg [127:0] key1;
    reg [127:0] in_text;

    // Outputs
    wire [127:0] out_128;

    // Instantiate the Unit Under Test (UUT)
    encryptor_top uut (
        .clk1(clk1),
        .key1(key1),
        .in_text(in_text),
        .out_128(out_128)
    );

    // Clock generation
    always begin
        #5 clk1 = ~clk1; // 10ns clock period (100 MHz)
    end

    // Test procedure
    initial begin
        // Initialize Inputs
        clk1 = 0;
        key1 = 128'h00000000000000000000000000000000;
        in_text = 128'h00000000000000000000000000000000;

        // Wait for a few clock cycles
        #10;

        // Test case 1: First key and input text
        key1 = 128'h2b7e151628aed2a6abf7158809cf4f3c; // Example key
        in_text = 128'h6bc1bee22e409f96e93d7e117393172a; // Example plaintext

        // Wait for the encryption to complete (assuming 10 clock cycles for example)
        #100;
        $display("Time: %0t | Key: %h | Input: %h | Output: %h", $time, key1, in_text, out_128);

        // End simulation
        $stop;
    end

endmodule
