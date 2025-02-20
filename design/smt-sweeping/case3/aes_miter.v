`include "aes-verilog/aes-verilog/Encrypt.v"
`include "AES-Verilog/AES_Encrypt.v"

module aes_miter(
    input wire clk,                    // 时钟信号
    input wire [127:0] Block,           // 输入数据块
    input wire [127:0] Key,             // AES 密钥
    output wire mismatch                // 比较结果信号（若不匹配，则为1）
);

    wire [127:0] result_encrypt, result_aes;  // 存储两个模块的输出结果

    // 实例化 Encrypt 模块
    Encrypt encrypt_instance (
        .Block(Block),
        .Key(Key),
        .Result(result_encrypt)
    );

    // 实例化 AES 模块
    AES #(128, 1, 4) aes_instance (
        .in(Block),
        .out(result_aes),
        .key128(Key)
    );

    // 比较 Encrypt 和 AES 模块的输出，如果不同，则 mismatch 信号为 1
    assign mismatch = (result_encrypt != result_aes);

endmodule
