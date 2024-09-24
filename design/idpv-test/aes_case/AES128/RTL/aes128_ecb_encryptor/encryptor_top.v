`timescale 1ns / 1ps
`include "encrypt_final_round.v"
`include "sub_bytes.v"
`include "shift_rows.v"
`include "encrypt_top.v"
`include "add_round_key.v"

module encryptor_top(
    input wire clk1, 
    input wire [127:0] key1,
    input wire [127:0] in_text,
    output wire [127:0] out_128   
);

    encrypt_top i_encrypt_top (
        .clk(clk1),
        .key(key1), 
        .plain_text(in_text), 
        .cipher_text(out_128)
    );


endmodule
