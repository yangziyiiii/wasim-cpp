`timescale 1ns / 1ps
module lcd(
input wire clk, 
input wire [0:127] line1,
input wire [0:127] line2,
output reg lcd_rw,
output reg lcd_e,
output reg lcd_rs,
output reg [7:0] data);
reg [7:0] data_o [1:38];
integer i = 0;
integer j = 1;
initial
begin
lcd_rw <= 0;
data_o[5'd1] <= 8'h38;
data_o[5'd2] <= 8'h0c;
data_o[5'd3] <= 8'h06;
data_o[5'd4] <= 8'h01;
data_o[5'd5] <= 8'h80;
data_o[5'd6] <= "R";
data_o[5'd7] <= "I";
data_o[5'd8] <= "T";
data_o[5'd9] <= "I";
data_o[5'd10] <= "K";
data_o[5'd11] <= " ";
data_o[5'd12] <= "C";
data_o[5'd13] <= "H";
data_o[5'd14] <= "A";
data_o[5'd15] <= "N";
data_o[5'd16] <= "N";
data_o[5'd17] <= "A";
data_o[5'd18] <= " ";
data_o[5'd19] <= " ";
data_o[5'd20] <= " ";
data_o[5'd21] <= " ";
data_o[5'd22] <= 8'hc0;
data_o[5'd23] <= "R";
data_o[5'd24] <= "I";
data_o[5'd25] <= "T";
data_o[5'd26] <= "I";
data_o[5'd27] <= "K";
data_o[5'd28] <= " ";
data_o[5'd29] <= "C";
data_o[5'd30] <= "H";
data_o[5'd31] <= "A";
data_o[32] <= "N";
data_o[33] <= "N";
data_o[34] <= "A";
data_o[35] <= " ";
data_o[36] <= " ";
data_o[37] <= " ";
data_o[38] <= " ";
end
always@ (posedge clk)

begin
data_o[6] <= line1[0:7];
data_o[7] <= line1[8:15];
data_o[8] <= line1[16:23];
data_o[9] <= line1[24:31];
data_o[10] <= line1[32:39];
data_o[11] <= line1[40:47];
data_o[12] <= line1[48:55];
data_o[13] <= line1[56:63];
data_o[14] <= line1[64:71];
data_o[15] <= line1[72:79];
data_o[16] <= line1[80:87];
data_o[17] <= line1[88:95];
data_o[18] <= line1[96:103];
data_o[19] <= line1[104:111];
data_o[20] <= line1[112:119];
data_o[21] <= line1[120:127];

data_o[23] <= line2[0:7];
data_o[24] <= line2[8:15];
data_o[25] <= line2[16:23];
data_o[26] <= line2[24:31];
data_o[27] <= line2[32:39];
data_o[28] <= line2[40:47];
data_o[29] <= line2[48:55];
data_o[30] <= line2[56:63];
data_o[31] <= line2[64:71];
data_o[32] <= line2[72:79];
data_o[33] <= line2[80:87];
data_o[34] <= line2[88:95];
data_o[35] <= line2[96:103];
data_o[36] <= line2[104:111];
data_o[37] <= line2[112:119];
data_o[38] <= line2[120:127];
lcd_rw = 0;
if (i <= 10000)
begin
i <= i + 1;
lcd_e <= 1;
data <= data_o[j];
end
else if (i > 10000 & i < 20000) 
begin
i <= i + 1;
lcd_e <= 0;
end
else if (i == 20000) 
begin
j <= j + 1;
i <= 0;
end
if (j <= 5 | j==22) lcd_rs <= 0;
else if (j > 5) lcd_rs <= 1;
if (j == 39) j <= 5;
end 
endmodule