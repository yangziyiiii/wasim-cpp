module encrypt_top(
    input wire clk,
    input wire [127:0] key,
    input wire [127:0] plain_text,
    output wire [127:0] cipher_text
);

    wire [127:0] enc_state_final_round_out;

    assign cipher_text = enc_state_final_round_out;

    encrypt_final_round i_encrypt_final_round(
        .clk(clk), 
        .round_key(key),
        .state_in(plain_text),
        .state_round(enc_state_final_round_out)
    );

endmodule
