`timescale 1ns/1ps
`include "miter.v"
module tb_miter;

  // 信号声明
  reg         clk;
  reg         reset;
  reg [127:0] key;
  reg [127:0] cipher;
  wire        mismatch;

  // 实例化待验证的 miter 模块
  miter uut (
    .clk(clk),
    .reset(reset),
    .key(key),
    .cipher(cipher),
    .mismatch(mismatch)
  );

  // 时钟生成：周期 10ns
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // 仿真激励
  initial begin
    // 初始复位以及测试向量赋值
    $dumpfile("wave.vcd");
    $dumpvars(0, tb_miter);
    reset  = 1;
    // 这里使用一个常见的测试向量（例如 AES-128 标准测试向量）
    key    = 128'h000102030405060708090A0B0C0D0E0F;
    cipher = 128'h69c4e0d86a7b0430d8cdb78070b4c55a;

    // 保持复位一段时间，确保模块内部状态初始化
    #20;
    reset = 0;

    // 等待足够的时间让解密过程完成（视具体实现而定，可适当调整等待时间）
    #2000;

    // 输出测试结果：若 mismatch 为 0 表示两个解密模块的输出一致
    if (mismatch)
      $display("Test FAILED: mismatch = 1");
    else
      $display("Test PASSED: mismatch = 0");



    $finish;
  end

endmodule
