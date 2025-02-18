module ALU(input [63:0] a, input [63:0] b, input [4:0] cond, output [127:0] out);

wire [63:0] internal_a1, internal_a2, internal_b;

assign internal_a1 = cond[1:0] == 2'b00	? a << 1 :
			        (cond[1:0] == 2'b01)? {1'b0, a[62:0]} :
			        (cond[1:0] == 2'b10)? {a[63:1], 1'b0} : a & b;

assign internal_a2 =  (cond[2] == 1'b0) ? { a[63], internal_a1[63:1]} : a | b;

assign out = (cond[4:3] == 2'b00) ? {internal_a2 + b} :
                (cond[4:3] == 2'b01) ? {internal_a2 - b} :
                (cond[4:3] == 2'b10) ? {internal_a2 * b} :
                {internal_a2 / b};
// when control is 5'b10000, alu is same as alu_golden
endmodule
