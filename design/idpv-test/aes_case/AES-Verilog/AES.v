`include "addRoundKey.v"
`include "subBytes.v"
`include "shiftRows.v"
`include "encryptRound.v"
`include "mixColumns.v"
`include "keyExpansion.v"
`include "sbox.v"
`include "AES_Encrypt.v"

module AES(in,out,key128);

input [127:0]in;
output [127:0]out;
input [127:0]key128;


AES_Encrypt a(in,key128,out);


endmodule