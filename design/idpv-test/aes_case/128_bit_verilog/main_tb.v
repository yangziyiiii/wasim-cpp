`timescale 1ns / 1ps

module main_tb;

    // Inputs
    reg [127:0] data;
    reg [127:0] key128;

    // Outputs
    wire [127:0] out128;

    // Instantiate the Unit Under Test (UUT)
    main uut (
        .data(data),
        .key128(key128),
        .out128(out128)
    );

    // Test procedure
    initial begin
        // Initialize Inputs
        data = 128'h00000000000000000000000000000000;
        key128 = 128'h00000000000000000000000000000000;

        // Wait for a few clock cycles
        #10;

        // Test case 1: First key and input data
        data = 128'h6bc1bee22e409f96e93d7e117393172a;  // Example plaintext
        key128 = 128'h2b7e151628aed2a6abf7158809cf4f3c; // Example key

        // Wait for encryption to complete
        #100;
        $display("Time: %0t | Key: %h | Input: %h | Output: %h", $time, key128, data, out128);

        // End simulation
        $stop;
    end

endmodule
