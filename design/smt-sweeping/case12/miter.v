module miter_aes_decrypter(
    input  [127:0] CipherText,  // 输入密文
    input  [127:0] key,         // 密钥
    output         result       // 比较结果：0 表示一致，1 表示不一致
);

wire [127:0] plainText1;
wire [127:0] plainText2;

// 实例化 AES_Decrypter_1 模块
AES_Decrypter_1 u_decrypter1 (
    .CipherText(CipherText),
    .key(key),
    .PlainText(plainText1)
);

// 实例化 AES_Decrypt 模块（参数：N=128, Nr=10, Nk=4）
AES_Decrypt #(.N(128), .Nr(10), .Nk(4)) u_decrypt2 (
    .in(CipherText),
    .key(key),
    .out(plainText2)
);

// 通过 XOR 对比两个模块的输出
wire [127:0] miter_out;
assign miter_out = plainText1 ^ plainText2;

// OR-reduce，若所有位均为 0，则 result 为 0（表示一致）；否则 result 为 1（表示有差异）
assign result = |miter_out;

endmodule
