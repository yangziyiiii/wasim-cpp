`timescale 1ns / 1ps

`include "encrypt_round.v"
`include "add_round_key.v"
`include "sub_bytes.v"
`include "shift_rows.v"
`include "mix_columns.v"

module encrypt_top(
    input wire clk,
    input wire reset,
    input wire [127:0] key,
    input wire [127:0] round1_key, 
    input wire [127:0] plain_text,
    output wire [127:0] cipher_text
	);
	
	wire [127:0] enc_state_in;	
	wire [127:0] enc_state_round1_out;

	reg [127:0] enc_state_round1_reg, enc_state_round1_next;
	
	always @(posedge clk)
    begin
        enc_state_round1_reg <= enc_state_round1_next;
    end
	
	always @*
    begin
    	//Combinational logic
		enc_state_round1_next = enc_state_round1_out;
	    
    end


    add_round_key i_add_round_key(
	    . clk(clk), 
	    . reset(reset),
	    . round_key(key),
	    . state_ark_in(plain_text),
	    . state_ark_out(enc_state_in));
    
	encrypt_round i_encrypt_round_1(
		. clk(clk), 
		. reset(reset),
		. round_key(round1_key),
		. enc_state_in(enc_state_in),
		. enc_state_round(enc_state_round1_out));
	
	
    
    assign cipher_text = enc_state_round1_reg;
    
	endmodule