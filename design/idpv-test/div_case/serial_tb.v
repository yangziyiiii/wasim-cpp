`timescale 1ns / 1ps

module tb_serial_divide_uu;

parameter M_PP = 16;          
parameter N_PP = 8;          
parameter R_PP = 0;           
parameter S_PP = 0;           
parameter COUNT_WIDTH_PP = 5;


reg clk_i;
reg clk_en_i;
reg rst_i;
reg divide_i;
reg [M_PP-1:0] dividend_i;
reg [N_PP-1:0] divisor_i;


wire [M_PP+R_PP-S_PP-1:0] quotient_o;
wire done_o;

serial_divide_uu #(
    .M_PP(M_PP),
    .N_PP(N_PP),
    .R_PP(R_PP),
    .S_PP(S_PP),
    .COUNT_WIDTH_PP(COUNT_WIDTH_PP)
) uut (
    .clk_i(clk_i),
    .clk_en_i(clk_en_i),
    .rst_i(rst_i),
    .divide_i(divide_i),
    .dividend_i(dividend_i),
    .divisor_i(divisor_i),
    .quotient_o(quotient_o),
    .done_o(done_o)
);


initial begin
    clk_i = 0;
    forever #10 clk_i = ~clk_i;  
end


initial begin
    rst_i = 1;
    #100;
    rst_i = 0;
end


initial begin
    clk_en_i = 0;
    divide_i = 0;
    dividend_i = 0;
    divisor_i = 0;
    $dumpfile("wave.vcd");      
    $dumpvars(0, tb_serial_divide_uu); 

    #150;
    
    clk_en_i = 1;
    
    #20;
    
    dividend_i = 16'b0000000000000000;
    divisor_i = 8'b00000001;
    divide_i = 1;
    
    #20;
    
    divide_i = 0;
    wait(done_o == 1);
    $display("Test Case 1: Dividend = %d, Divisor = %d, Quotient = %d", dividend_i, divisor_i, quotient_o);
    
    #100;
    $finish;
    
end

endmodule
