`default_nettype none

module ALU(input [31:0] a, input [31:0] b, input [4:0] cond, output [63:0] out);

wire [31:0] internal_a1, internal_a2;
wire [31:0] internal_b;

assign internal_a1 = cond[1:0] == 2'b00 ? a << 1 :
                    (cond[1:0] == 2'b01) ? {1'b0, a[30:0]} :
                    (cond[1:0] == 2'b10) ? {a[31:1], 1'b0} : a & b;

assign internal_a2 =  (cond[2] == 1'b0) ? { a[31], internal_a1} - {1'b0, a} : b;

assign internal_b = b;

assign out = cond[4:3] == 2'b00 ? internal_a2 + internal_b :
            cond[4:3] == 2'b01 ? internal_a2 - internal_b :
            cond[4:3] == 2'b10 ? internal_a2 * internal_b : internal_a2 / internal_b;

endmodule


module alu_golden(input [31:0] a, input [31:0] b, output [63:0] out);

assign out = a / b;

endmodule

module alu_miter(input [31:0] a, input [31:0] b, input [4:0] control, output result, output condition);

wire [63:0] alu_out;
wire [63:0] alu_golden_out;
wire [63:0] miter_out;

ALU ALU(.a(a), .b(b), .cond(control), .out(alu_out));
alu_golden alu_golden(.a(a), .b(b), .out(alu_golden_out));

assign miter_out = alu_out ^ alu_golden_out;
assign result = |miter_out;
assign condition = (control == 5'b11000) ? 1'b1 : 1'b0;

endmodule