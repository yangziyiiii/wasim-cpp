`timescale 1ns / 1ps

module ALU_tb;
    // Declare testbench signals
    reg [63:0] a, b;
    reg [4:0] control;
    wire [127:0] out;

    // Instantiate the ALU module
    ALU uut (
        .a(a),
        .b(b),
        .control(control),
        .out(out)
    );

    // Monitor internal signals for testing
    wire [63:0] internal_a1, internal_a2;
    assign internal_a1 = uut.internal_a1;
    assign internal_a2 = uut.internal_a2;

    // Initial block to set up the testbench
    initial begin
        // Apply some test values to a, b, and control
        a = 64'b1111111111111111111111111111111111111111111111111111111111111111;  // Example input for a
        b = 64'b1111111111111111111111111111111111111111111111111111111111111111;  // Example input for b
        control = 5'b00000;        // Example control signal

        // Monitor the outputs
        $monitor("Time: %0t | a: %h | b: %h | control: %b | internal_a1: %h | internal_a2: %h | out: %h", 
                 $time, a, b, control, internal_a1, internal_a2, out);

        // Apply some test cases with different control values
        #10 control = 5'b10000;  // Test case 6
        #10 $finish;  // End the simulation
    end
endmodule
