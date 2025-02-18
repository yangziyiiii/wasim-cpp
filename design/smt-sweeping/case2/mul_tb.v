module ALU_tb;

    // 输入信号
    reg [63:0] a, b;
    reg [4:0] cond;
    
    // 输出信号
    wire [127:0] out;
    
    // 实例化 ALU 模块
    ALU uut (
        .a(a),
        .b(b),
        .cond(cond),
        .out(out)
    );
    
    // 初始化信号
    initial begin
        // 初始化输入
        a = 64'b0;
        b = 64'b0;
        cond = 5'b00000;
        
        // 打印测试开始
        $display("Testing ALU...");

        // 等待时间
        #10;
        
        // 测试 1: 左移操作 (cond = 00000)
        a = 64'h0000000000000010;  // a = 16
        b = 64'h0000000000000000;  // b = 0
        cond = 5'b00000;           // 左移操作 (a << 1)
        #10;                       // 等待 10 时间单位
        $display("Test 1: a = %h, b = %h, cond = %b, out = %h", a, b, cond, out);

        // 测试 2: 位移加前补零操作 (cond = 00001)
        cond = 5'b00001;           // {1'b0, a[62:0]} 操作
        #10;
        $display("Test 2: a = %h, b = %h, cond = %b, out = %h", a, b, cond, out);

        // 测试 3: 右移并在尾部加零操作 (cond = 00010)
        cond = 5'b00010;           // {a[63:1], 1'b0} 操作
        #10;
        $display("Test 3: a = %h, b = %h, cond = %b, out = %h", a, b, cond, out);

        // 测试 4: 按位与操作 (cond = 00011)
        cond = 5'b00011;           // a & b 操作
        a = 64'hF0F0F0F0F0F0F0F0;  // 设置 a 为一些非零值
        b = 64'h0F0F0F0F0F0F0F0F;  // 设置 b 为另一个非零值
        #10;
        $display("Test 4: a = %h, b = %h, cond = %b, out = %h", a, b, cond, out);

        // 测试 5: 减法操作 (cond = 00100)
        cond = 5'b00100;           // { a[63], internal_a1} - {1'b0, a} 操作
        a = 64'hA5A5A5A5A5A5A5A5;  // a 的值为一个特定值
        b = 64'h0000000000000005;  // b 的值为 5
        #10;
        $display("Test 5: a = %h, b = %h, cond = %b, out = %h", a, b, cond, out);

        // 测试 6: 按位或操作 (cond = 00101)
        cond = 5'b00101;           // a | b 操作
        #10;
        $display("Test 6: a = %h, b = %h, cond = %b, out = %h", a, b, cond, out);

        // 测试 7: 加法操作 (cond = 01000)
        cond = 5'b01000;           // internal_a2 + b 操作
        a = 64'h000000000000000A;  // a = 10
        b = 64'h0000000000000005;  // b = 5
        #10;
        $display("Test 7: a = %h, b = %h, cond = %b, out = %h", a, b, cond, out);

        // 测试 8: 减法操作 (cond = 01001)
        cond = 5'b01001;           // internal_a2 - b 操作
        #10;
        $display("Test 8: a = %h, b = %h, cond = %b, out = %h", a, b, cond, out);

        // 测试 9: 乘法操作 (cond = 01010)
        cond = 5'b01010;           // internal_a2 * b 操作
        a = 64'h0000000000000003;  // a = 3
        b = 64'h0000000000000004;  // b = 4
        #10;
        $display("Test 9: a = %h, b = %h, cond = %b, out = %h", a, b, cond, out);

        // 测试 10: 除法操作 (cond = 01011)
        cond = 5'b01011;           // internal_a2 / b 操作
        a = 64'h0000000000000030;  // a = 48
        b = 64'h0000000000000008;  // b = 8
        #10;
        $display("Test 10: a = %h, b = %h, cond = %b, out = %h", a, b, cond, out);

        // 打印测试完成
        $display("Test Complete");
        $finish;
    end

endmodule
