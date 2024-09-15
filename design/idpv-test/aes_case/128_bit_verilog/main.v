`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    12:11:38 06/10/2017 
// Design Name: 
// Module Name:    main 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

`include "sub_byte.v"
`include "mix_col.v"
`include "key_gen.v"
`include "sbox.v"

module main(data,key128,out128);//
input [0:127] data,key128;
output [0:127] out128;

wire [0:127] s_key0; 
wire [0:127] mx_key0; 
wire [0:127] gen_key0; 
wire [0:127] pr_key;
//pre round operation

assign pr_key = data^key128;

sub_byte s0(pr_key,s_key0);

//mix column

mix_col  m0(s_key0,mx_key0);

//add round key operation

key_gen k0(key128, mx_key0, 32'h01000000, gen_key0, out128);

endmodule
