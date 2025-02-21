	`timescale 1ns / 1ps
	module TestBench(
	input wire clk, 
output reg lcd_rw,
output reg lcd_e,
output reg lcd_rs,
output reg [7:0] data);
	
	reg [127:0] TestState;
	reg [127:0] TestKey;
	wire [127:0] TestResult;
	Decrypt e_module(TestState,TestKey,TestResult);
	initial
	begin
	TestState=127'h12edf70abe44d3596c48a1da8fc224d7;
	TestKey=128'h000102030405060708090a0b0c0d0e0f;
	//assign led = TestState[127];
	end
function [7:0] hex2ASCII;
input[3:0] signal; 

begin
if (signal >= 4'h0 && signal <= 4'h9 )
begin
 hex2ASCII = signal + 8'h30;
end //end if for 0-9

else if  ( signal >= 4'ha && signal <= 4'hf )
begin
 hex2ASCII = signal + 8'h57;
end// end of elseif for a-f

else
begin
 hex2ASCII = 8'h3f; // 3f = ? in ASCII 
end// end else
end // end function begin
endfunction //end function hexa2ASCII
endmodule
