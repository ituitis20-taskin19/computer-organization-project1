`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: ÝTÜ
// Engineer: Aybike Zeynep Taþkýn 150190004 Feray Lina Yence 150190007 Mevlüt Erdoðdu 150180051
// Create Date: 08.05.2022 15:14:53D
// Design Name: 
// Module Name: Modules
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module Modules();
endmodule

module eight_bit_register(
 input [7:0] I,
 input enable,
 input [1:0] FunSel,
 input clk,  
 output [7:0] reg_out
 );
    reg [7:0]temp;
    wire [7:0] itemp;
    assign itemp = reg_out;
    always@(posedge clk)
    begin //MUX:
    if(enable)begin
        case(FunSel)
            2'b00: temp = itemp - 8'b00000001;
            2'b01: temp = itemp + 8'b00000001;
            2'b10: temp = I;
            2'b11: temp = 8'b00000000;
        endcase
    end
    end
    assign reg_out = temp;   
endmodule

module sixteen_bit_register(
 input [15:0] I,
 input enable,
 input [1:0] FunSel,
 input clk,  
 output [15:0] reg_out
 );
    reg [15:0]temp;
    wire [15:0] itemp;
    assign itemp = reg_out;
    always@(posedge clk)
    begin
    if(enable)begin // 16 bit MUX:
        case(FunSel)
            2'b00: temp = itemp - 16'b0000000000000001;
            2'b01: temp = itemp + 16'b0000000000000001;
            2'b10: temp = I;
            2'b11: temp = 16'b0000000000000000;
        endcase
    end
    end
    assign reg_out = temp;   
endmodule

module Part2A(
    input [7:0] I,
    input [1:0] outASel,
    input [1:0] outBSel,
    input [1:0] FunSel,
    input [3:0] RegSel,
    input [0:0] clock,
    output [7:0] outAData,
    output [7:0] outBData
);
wire [3:0] RegSel_compl; 
assign RegSel_compl = ~RegSel;
wire [7:0] outR1;
wire [7:0] outR2;
wire [7:0] outR3;
wire [7:0] outR4;
eight_bit_register R1(I, RegSel_compl[0:0], FunSel,  clock, outR1);
eight_bit_register R2(I, RegSel_compl[1:1], FunSel,  clock, outR2);
eight_bit_register R3(I, RegSel_compl[2:2], FunSel,  clock, outR3);
eight_bit_register R4(I, RegSel_compl[3:3], FunSel,  clock, outR4);
MUX4to1 m1(outR1, outR2, outR3, outR4, outASel, outAData);
MUX4to1 m2(outR1, outR2, outR3, outR4, outBSel, outBData);

endmodule

module MUX4to1(
    input [7:0]in0, [7:0]in1, [7:0]in2, [7:0]in3,
    input [1:0]FunSel,
    output reg [7:0] out
    //input enable
    );
    always@(in0 or in1 or in2 or in3 or FunSel)
    //if(enable)
    begin
        case(FunSel)
            2'b00:out <= in0;
            2'b01:out <= in1;
            2'b10:out <= in2;
            2'b11:out <= in3;
        endcase
    end
endmodule

module address_register(
    input [7:0] I, input [1:0] FunSel, input clk, 
    input [2:0] RegSel,
    input [1:0] OutCSel,
    input [1:0] OutDSel,
    output [7:0] OutC,
    output [7:0] OutD
    );
    wire [7:0] PC_reg_out;
    wire [7:0] AR_reg_out;
    wire [7:0] SP_reg_out;   
    wire RegSel_1, RegSel_2, RegSel_3, NegRegSel_1, NegRegSel_2, NegRegSel_3;
    assign RegSel_1 = RegSel[2:2];
    assign RegSel_2 = RegSel[1:1];
    assign RegSel_3 = RegSel[0:0];
    not_gate not1(.a(RegSel_1), .o(NegRegSel_1));
    not_gate not2(.a(RegSel_2), .o(NegRegSel_2));
    not_gate not3(.a(RegSel_3), .o(NegRegSel_3));
    eight_bit_register PC(I, NegRegSel_1, FunSel, clk, PC_reg_out);
    eight_bit_register AR(I, NegRegSel_2, FunSel, clk, AR_reg_out);
    eight_bit_register SP(I, NegRegSel_3, FunSel, clk, SP_reg_out);
    MUX4to1 mux1(PC_reg_out, PC_reg_out, AR_reg_out, SP_reg_out, OutCSel, OutC);
    MUX4to1 mux2(PC_reg_out, PC_reg_out, AR_reg_out, SP_reg_out, OutDSel, OutD);
endmodule

module not_gate(
    input a,
    output o
    );
    
    assign o = ~a;
endmodule


module Part_two_C(
    input [7:0] I,
    input enable,
    input [1:0] FunSel,
    input clk, LH, 
    output [15:0] reg_out
    );
    wire [15:0]input_reg_mux;
    reg [15:0] itemp;
    wire temp_out;
    wire [15:0]tempreg;
    assign tempreg = reg_out;
    //if LH=0 load I to MSB if 1 load to LSB 
    always @(*)
    begin
      if (LH)
        itemp = {tempreg[15:8],I[7:0]};
      else
        itemp = {I[7:0],tempreg[7:0]};
    end
    assign input_reg_mux = itemp;
    sixteen_bit_register sixteenbitreg(input_reg_mux, enable, FunSel, clk, reg_out);
endmodule

module Memory(
    input wire[7:0] address,
    input wire[7:0] data,
    input wire wr, //Read = 0, Write = 1
    input wire cs, //Chip is enable when cs = 0
    input wire clock,
    output reg[7:0] o // Output
);
    //Declaration oýf the RAM Area
    reg[7:0] RAM_DATA[0:255];
    //Read Ram data from the file
    initial $readmemh("RAM.mem", RAM_DATA);
    //Read the selected data from RAM
    always @(*) begin
        o = ~wr && ~cs ? RAM_DATA[address] : 8'hZ;
    end
    
    //Write the data to RAM
    always @(posedge clock) begin
        if (wr && ~cs) begin
            RAM_DATA[address] <= data; 
        end
    end
endmodule


module MUX2to1(
    input [7:0]in0, [7:0]in1,
    input LH,
    output reg [7:0] out
    );
    always@(in0 or in1 or LH)
    begin
        case(LH)
            1'b0:out <= in0;
            1'b1:out <= in1;
        endcase
    end
endmodule

module MUX16to1( input[7:0] i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15,
    input[3:0]FunSel,
    output[7:0] out);
    
    wire[7:0] o1, o2, o3, o4;
    
    MUX4to1 M1(i0, i1, i2, i3, FunSel[1:0], o1);
    MUX4to1 M2(i4, i5, i6, i7, FunSel[1:0], o2);
    MUX4to1 M3(i8, i9, i10, i11, FunSel[1:0], o3);
    MUX4to1 M4(i12, i13, i14, i15, FunSel[1:0],o4);
    
    MUX4to1 M5(o1, o2, o3, o4, FunSel[3:2], out);
endmodule

/*module ALU_Part3(
    input [7:0] A, B, [3:0] FunSel, [0:0]c_in, [0:0]clk,
    output [7:0] OutALU, [3:0] flag_out
    );
    reg [3:0]flags;
    wire oFlow1, oFlow2, oFlow3, oFlow4, oFlow5, oFlow6, oFlow;
    wire c1, c2, c3, c4, c5, c6, c7, C;
    wire Zflag;
    wire Nflag;
    wire [7:0] case0, case1, case2, case3, case4, case5, case6, case7, case8, case9, case10, case11, case12, case13, case14, case15;
    wire [7:0] dec4, dec5, dec6, dec10, dec11, dec12, dec13, dec14, dec15;
    wire [0:16] dec_out;
    
    decoder4to16 Dec1(FunSel, dec_out);
    assign dec4 = dec_out[4:4];
    assign dec5 = dec_out[5:5];
    assign dec6 = dec_out[6:6];
    assign dec10 = dec_out[10:10];
    assign dec11 = dec_out[11:11];
    assign dec12 = dec_out[12:12];
    assign dec13 = dec_out[13:13];
    assign dec14 = dec_out[14:14];
    assign dec15 = dec_out[15:15];
    
    assign case0 = A;
    
    assign case1 = B;
    
    assign case2 = ~A;
    
    assign case3 = ~B;
    
    wire AplusB;
    assign AplusB = A + B;
    assign {c1, case4} = AplusB;
    
    overflow oflow1(A[7:7],B[7:7],1'b0,case4[7:7],oFlow1);
    wire AplusBplusC;
    assign AplusBplusC = A + B + c_in;
    assign {c2,case5} = AplusBplusC;
    
    overflow oflow2(A[7:7],B[7:7],c_in,case5[7:7],oFlow2);
    wire AminusB;
    assign AminusB = A - B;
    assign {c3,case6} = AminusB;
    
    overflow oflow3(A[7:7],~B[7:7],1'b1,case6[7:7],oFlow3);
    assign case7 = A & B;
    
    assign case8 = A | B;
    
    assign case9 = A ^ B;
    
    assign case10 = A<<1; 
    assign c4 = A[7:7];
    
    assign case11 = A>>1;
    assign c5 = A[0:0];
    
    assign case12 = A<<<1;
    assign oFlow4 = A[7:7];
    
    assign case13 = A>>>1;
    
    wire temp1;
    assign temp1 = {A, c_in};
    assign {c6,case14} = temp1;
    assign oFlow5 = A[7:7]^case14[7:7];
    
    wire temp2;
    assign temp2 = {c_in, A}; 
    assign {c7,case15} = temp2;
    assign oFlow6 = A[7:7]^case15[7:7];
    
    assign oFlow = (oFlow1&dec4)|(oFlow2&dec5)|(oFlow3&dec6)|(oFlow4&dec12)|(oFlow5&dec14)|(oFlow6&dec15);
    assign C = (c1&dec4)|(c2&dec5)|(c3&dec6)|(c4&dec10)|(c5&dec11)|(c6&dec14)|(c7&dec15);
    
    MUX16to1 M1(case0, case1, case2, case3, case4, case5, case6, case7, case8, case9, case10, case11, case12, case13, case14, case15, FunSel, OutALU);
    assign Zflag =~(OutALU[0:0] | OutALU[1:1] | OutALU[2:2] | OutALU[3:3] | OutALU[4:4] | OutALU[5:5] | OutALU[6:6] | OutALU[7:7]);
    assign Nflag = OutALU[7:7]&(~dec13);
    always @(posedge clk)
        begin
        flags[3:3] = Zflag;
        flags[2:2] = C;
        flags[1:1] = Nflag;
        flags[0:0] = oFlow;
    end
    assign flag_out = flags;    
    endmodule

*/

module ALU_Part3(
         input [7:0] A,B,OutALU,                   
         input [3:0] FunSel,flag_out,
         input c_in,
         input clock
         );
        reg [3:0]flags;
        wire oFlow1,oFlow2,oFlow3,oFlow4,oFlow5,oFlow6,oFlow;
        wire [7:0] case0,case1,case2,case3,case4,case5,case6,case7,case8,case9,case10,case11,case12,case13,case14,case15; //results
        wire dec4,dec5,dec6,dec10,dec11,dec12,dec13,dec14,dec15;       
        wire c1,c2,c3,c4,c5,c6,c7, cFlag;
        wire ZFlag, NFlag;
        
        assign case0 = A;
               
        assign case1 = B;
               
        assign case2 = ~A;
               
        assign case3 = ~B;
        
        
        wire [15:0] dec_out;
        decoder4to16 Dec1(FunSel, dec_out);
                
        assign dec4 = dec_out[4];
        assign dec5 = dec_out[5];
        assign dec6 = dec_out[6];
        assign dec10 = dec_out[10];
        assign dec11 = dec_out[11];
        assign dec12 = dec_out[12];
        assign dec13 = dec_out[13];
        assign dec14 = dec_out[14]; 
        assign dec15 = dec_out[15]; 
        
        
        assign {c1,case4} = A + B;
        overflow overflow1(A[7],B[7],1'b0,case4[7],oFlow1);
        
        assign {c2,case5} = A + B + c_in;
        overflow overflow2(A[7],B[7],1'b0,case5[7],oFlow2);
        
        assign {c3,case6} = A + (~B)+1;
        overflow overflow3(A[7:7],B[7:7],1'b1,case6[7:7],oFlow3);
        
        assign case7 = A & B;
        
        assign case8 = A | B;
        
        assign case9 = A ^ B;
        
        assign case10 = A<<1; //LSL
        assign c4 = A[7:7];
        
        assign case11 = A>>1; //LSR
        assign c5 = A[0:0];
        
        assign case12 = A<<<1; //ASL
        assign oFlow4 = A[7:7]^case12[7];
        
        assign case13 = A>>>1; //ASR
        assign {c6,case14} = {A,c_in}; //CSL
        
        assign oFlow5 = A[7:7]^case14[7];
        assign {case14,c7} = {c_in,A}; //CSR
        
        assign oFlow6 = A[7]^case14[7];
        
        assign cFlag = (c1&dec4)|(c2&dec5)|(c3&dec6)|(c4&dec10)|(c5&dec11)|(c6&dec14)|(c7&dec15); 
        assign ZFlag =~(OutALU[0:0]|OutALU[1:1]|OutALU[2:2]|OutALU[3:3]|OutALU[4:4]|OutALU[5:5]|OutALU[6:6]|OutALU[7:7]);
        assign NFlag = OutALU[7:7]&(~dec13);
        
        MUX16to1 M1(case0,case1,case2,case3,case4,case5,case6,case7,case8,case9,case10,case11,case12,case13,case14,case15, FunSel, OutALU);
      
        wire if_overflow;
        assign if_overflow = (dec4|dec5|dec6|dec12|dec14|dec15);
        assign oFlow = (oFlow1&dec4)|(oFlow2&dec5)|(oFlow3&dec6)|(oFlow4&dec12)|(oFlow5&dec14)|(oFlow6&dec15); 
        wire if_carry;
        assign if_carry = (dec4|dec5|dec6|dec10|dec11|dec14|dec15);
        
        always @(posedge clock) begin
        flags[3] = ZFlag;
            if(if_overflow)
              begin
                  flags[0] = oFlow;
              end
            if(~dec13)
              begin
                  flags[1] = NFlag;
              end
            if(if_carry)
              begin
                  flags[2] = cFlag;
              end
        end
        assign flag_out = flags;    
endmodule


module decoder4to16 (input [3:0] select, output wire [15:0] out);

assign out[0]= ( ~select [3:3]) & (~select[2:2])& ( ~select[1:1]) &( ~select [0:0]);
assign out[1]= ( ~select [3:3]) & (~select[2:2])& ( ~select[1:1]) &( select [0:0]);
assign out[2]= ( ~select [3:3]) & (~select[2:2])& ( select[1:1]) &( ~select [0:0]);
assign out[3]= ( ~select [3:3]) & (~select[2:2])& ( select[1:1]) &( select [0:0]);
assign out[4]= ( ~select [3:3]) & (select[2:2])& ( ~select[1:1]) &( ~select [0:0]);
assign out[5]= ( ~select [3:3]) & (select[2:2])& ( ~select[1:1]) &( select [0:0]);
assign out[6]= ( ~select [3:3]) & (select[2:2])& ( select[1:1]) &( ~select [0:0]);
assign out[7]= ( ~select [3:3]) & (select[2:2])& ( select[1:1]) &( select [0:0]);
assign out[8]= ( select [3:3]) & (~select[2:2])& ( ~select[1:1]) &( ~select [0:0]);
assign out[9]= ( select [3:3]) & (~select[2:2])& ( ~select[1:1]) &( select [0:0]);
assign out[10]= ( select [3:3]) & (~select[2:2])& ( select[1:1]) &( ~select [0:0]);
assign out[11]= ( select [3:3]) & (~select[2:2])& ( select[1:1]) &( select [0:0]);
assign out[12]= ( select [3:3]) & (select[2:2])& ( ~select[1:1]) &( ~select [0:0]);
assign out[13]= ( select [3:3]) & (select[2:2])& ( ~select[1:1]) &( select [0:0]);
assign out[14]= ( select [3:3]) & (select[2:2])& ( select[1:1]) &( ~select [0:0]);
assign out[15]= ( select [3:3]) & (select[2:2])& ( select[1:1]) &( select [0:0]);

endmodule

module decoder3to8 (input [2:0] select, output wire [7:0] out);

assign out[0]= (~select[2:2])& ( ~select[1:1]) &( ~select [0:0]);
assign out[1]= (~select[2:2])& ( ~select[1:1]) &( select [0:0]);
assign out[2]= (~select[2:2])& ( select[1:1]) &( ~select [0:0]);
assign out[3]= (~select[2:2])& ( select[1:1]) &( select [0:0]);
assign out[4]= (select[2:2])& ( ~select[1:1]) &( ~select [0:0]);
assign out[5]= (select[2:2])& ( ~select[1:1]) &( select [0:0]);
assign out[6]= (select[2:2])& ( select[1:1]) &( ~select [0:0]);
assign out[7]= (select[2:2])& ( select[1:1]) &( select [0:0]);

endmodule

module decoder2to4 (input [1:0] select, output wire [3:0] out);

assign out[0]= ( ~select[1:1]) &( ~select [0:0]);
assign out[1]= ( ~select[1:1]) &( select [0:0]);
assign out[2]= ( select[1:1]) &( ~select [0:0]);
assign out[3]= ( select[1:1]) &( select [0:0]);

endmodule


module overflow(
    input signA, signB, c_in, signResult,
    output oFlow
    );
    wire and1, and2, and3, and4;
    assign and1 = (~signA) & (~signB) & (~c_in) & (signResult);
    assign and2 = (signA) & (signB) & (~c_in) & (~signResult);
    assign and3 = (~signA) & (signB) & (c_in) & (signResult);
    assign and4 = (signA) & (~signB) & (c_in) & (~signResult);
    assign oFlow = and1 | and2 | and3 | and4;
endmodule


module ALUSystem(
    input IR_LH, IR_Enable, [1:0]MuxASel, [1:0]MuxBSel,[0:0]MuxCSel, [1:0]RF_FunSel, [1:0]ARF_FunSel, [1:0]IR_Funsel,
    input [1:0]ARF_OutCSel, [1:0]ARF_OutDSel, [2:0]ARF_RegSel,[1:0]RF_OutASel,[1:0]RF_OutBSel,
    input [3:0]RF_RegSel, [3:0]ALU_FunSel,
    input Mem_WR, Mem_CS, Clock, 
    output [7:0] AOut, BOut, ALUOut, Address, MemoryOut, MuxAOut, MuxBOut, MuxCOut,
    output [3:0]  ALUOutFlag,//?????
    output [15:0] IROut, //??
    output [7:0]ARF_Cout//isim yanlýþ olmuþ
    );

    wire [7:0] IR_lsb;
    wire [7:0] IR_msb;
    MUX2to1 MUXC(ARF_Cout, AOut,MuxCSel,MuxCOut);
    ALU_Part3 alu1(MuxCOut, BOut, ALUOut, ALU_FunSel, ALUOutFlag, ALUOutFlag[2], Clock);//????
    Part2A Register_File(MuxAOut, RF_OutASel, RF_OutBSel, RF_FunSel, RF_RegSel, Clock, AOut, BOut);
    MUX4to1 MUXA(IR_lsb, MemoryOut , ARF_Cout, ALUOut, MuxASel, MuxAOut);
    MUX4to1 MUXB(8'd0, IR_lsb, MemoryOut , ARF_Cout,  MuxBSel, MuxBOut); //???
    Part_two_C Part2c(MemoryOut, IR_Enable, IR_Funsel, Clock, IR_LH, IROut);
    assign IR_msb = IROut[15:8];
    assign IR_lsb = IROut[7:0];
    address_register ARF1(MuxBOut, ARF_FunSel, Clock, ARF_RegSel, ARF_OutCSel, ARF_OutDSel, ARF_Cout, Address);
    Memory memory1(Address, ALUOut, Mem_WR, Mem_CS, Clock, MemoryOut);
endmodule


module SequentialCounter(
    input reset,
    input clk,
    output T0, T1, T2, T3, T4, T5, T6, T7 
);

    wire [7:0] out_mux;
    wire [7:0] eightbitreg_out;
    wire [7:0] decoder_out;
    //posedge??
    MUX2to1 MUX_sequence(8'd1, 8'd3, reset, out_mux ); 
    eight_bit_register eightbitreg_sequence(8'd0, 1'd1/*enable*/, out_mux[1:0], clk, eightbitreg_out);
    decoder3to8 decoder_sequence(eightbitreg_out[2:0], decoder_out);
    assign T0 = decoder_out[0];
    assign T1 = decoder_out[1];
    assign T2 = decoder_out[2];
    assign T3 = decoder_out[3];
    assign T4 = decoder_out[4];
    assign T5 = decoder_out[5];
    assign T6 = decoder_out[6];
    assign T7 = decoder_out[7];    
    
endmodule

module Fetch(
    input T0, T1,
    output reg [1:0]ARF_OutDSel, ARF_FunSel, IR_Funsel, //RF_FunSel,
    output reg [2:0]ARF_RegSel,  
    output reg Mem_WR, Mem_CS,
    output reg [0:0] IR_Enable, IR_LH, Reset,
    output reg  [3:0]RF_RegSel  
    );
    
   always @(*) begin
    if(T0) begin
        ARF_OutDSel=0;//OutDSel=0;
        ARF_RegSel=3;
        ARF_FunSel=1;
        Mem_CS=0;//enable
        Mem_WR=0;//read
        IR_Enable=1;//IREnable=1;
        IR_Funsel=2;//IRFunSel=2;
        IR_LH=1;//LH=1;
        RF_RegSel=15;//RegFileRegSel=15;//
        Reset=0;        
    end
    else if(T1) begin
          ARF_OutDSel=0;//OutDSel=0;
          ARF_RegSel=3;//AddressRegSel=3;
          ARF_FunSel=1;//AddressFunSel=1;
          Mem_CS=0;//enable
          Mem_WR=0;//read
          IR_Enable=1;//IREnable=1;
          IR_Funsel=2;//IRFunSel=2;
          IR_LH=0;//LH=0;
          RF_RegSel=15;//RegFileRegSel=15;//f
          Reset=0;     
    end
   end
endmodule

module Decode(
    input  [15:0]Instruction,
    output [7:0]ADDRESS,
    output [1:0]REGSEL,
    output ADRESSINGMODE,
    output [3:0]OPCODE, SRCREG2,SRCREG1,DESTREG,
    output BRA, LD, ST, MOV, AND, OR, NOT, ADD, SUB, LSL, LSR, PUL, PSH, INC, DEC, BNE,
    output [7:0] out);
//instructions
assign ADDRESS = Instruction[7:0];
assign REGSEL = Instruction[9:8];
assign ADRESSINGMODE = Instruction[10];
assign OPCODE = Instruction[15:12];
 
assign SRCREG2 = Instruction[3:0];
assign SRCREG1 = Instruction[7:4];
assign DESTREG = Instruction[11:8];
    
//decode
reg [3:0]ALU_FunSel;
wire [15:0] decOut;
decoder4to16 Dec1(OPCODE, decOut);
    
assign BRA = decOut[0:0];
assign LD = decOut[1:1];
assign ST = decOut[2:2];
assign MOV = decOut[3:3];
assign AND = decOut[4:4];
assign OR = decOut[5:5];
assign NOT = decOut[6:6];
assign ADD = decOut[7:7];
assign SUB = decOut[8:8];
assign LSL = decOut[9:9];
assign LSR= decOut[10:10];
assign PUL= decOut[11:11];
assign PSH= decOut[12:12];
assign INC = decOut[13:13];
assign DEC= decOut[14:14];
assign BNE = decOut[15:15];

 always@(*)begin
    if(OPCODE==0||OPCODE==1||OPCODE==2||OPCODE==11||OPCODE==12||OPCODE==15)begin
     
        assign ALU_FunSel=0;
    end
    else if(OPCODE==13||OPCODE==14)begin
        //?????
    end
    else if(OPCODE==4)begin
          assign ALU_FunSel=7;
    end
        else if(OPCODE==5)begin
          assign ALU_FunSel=8;
    end
        else if(OPCODE==6)begin
      assign ALU_FunSel=2;
    end   
        else if(OPCODE==7)begin
     assign ALU_FunSel=4;
    end  
       else if(OPCODE==8)begin
    assign ALU_FunSel=6;
    end  
        else if(OPCODE==9)begin
     assign ALU_FunSel=10;
     end   
         else if(OPCODE==10)begin
  assign ALU_FunSel=11;
  end  
end

endmodule




//BRA: PC<-Value (IM)
//BNE: IF Z=0 then PC<-Value (IM)
//Value in Address field of IR(0-7) -> to PC
module BRA(
    input BRA,
    input AddressingMode, //IR[10]
    input T2,  
    output reg IR_Enable, Reset, 
    output reg [1:0] MuxBSel, ARF_FunSel, 
    output reg [2:0]ARF_RegSel, 
    output reg Mem_CS, Mem_WR,
    output reg [3:0]RF_RegSel
);
always@(*) begin
if(AddressingMode) begin
if((BRA & AddressingMode & T2)) begin
    MuxBSel = 1; //take IROut(0-7)
    ARF_RegSel = 3; 
    ARF_FunSel = 2; //load
    Mem_CS=0;//enable
    Mem_WR=0;//read?????????
    Reset=1;
    IR_Enable = 0;
    RF_RegSel = 15; //no regsiter enabled
end
end
else if(AddressingMode==0)begin
    if((BRA&~AddressingMode&T2))begin
        Reset=1;
    end
end
end
endmodule

module BNE(
    input AddressingMode, //IR[10]
    input T2, Z, BNE, 
    output reg IR_Enable, Reset, 
    output reg [1:0] MuxBSel, ARF_FunSel, 
    output reg [2:0]ARF_RegSel, 
    //output reg MemSel, MemStr, MemLd, //bunlarýn büyüklüðü idk
    output reg Mem_CS, Mem_WR,
    output reg [3:0]RF_RegSel//, RF_TmpSel//bunun büyüklüðü idk
);
always@(*) begin
//opcode???????
if(AddressingMode) begin
if((T2 & ~Z & BNE & AddressingMode)) begin
    MuxBSel = 1; //take IROut(0-7)
    ARF_RegSel = 3; //7 mi //R1 R2 enabled??? sadece R1 diil mi?? only PC should be enabled imo
    ARF_FunSel = 2; //load
    Mem_CS=0;//enable
    Mem_WR=0;//read?????????
    Reset=1;
    IR_Enable = 0;
    RF_RegSel = 15; //no regsiter enabled
end
end

else if(AddressingMode==0)begin
    if(((~AddressingMode&Z)&T2&BNE))begin
        Reset=1;
    end
end
end
endmodule

//M[SP]<-Rx, SP<-SP-1 (N/A)
//write register value Rx intp SP adrress reg then incrmeent by 1
module PSH( 
    input PSH, T2,
    input [3:0] DESTREG, //IR[11:8]
    input [3:0] DecodedALUFunSel, //????? normalde 4 bit ama decoded demiþ idk???
    output reg [1:0]RF_OutASel, ARF_OutDSel,
    output reg Mem_CS, Mem_WR,
    output reg [2:0]ARF_RegSel,
    output reg [0:0]Reset, IR_Enable, MuxCSel, 
    output reg [3:0]RF_RegSel, //RF_TmpSel,//??
    output reg [3:0]ALU_FunSel,
    output reg [1:0]ARF_FunSel

);
always@(*) begin
    if(PSH&T2) begin
        RF_OutASel = DESTREG[1:0];//reads destination register  from RF
        MuxCSel=1; //OutA
        ARF_OutDSel = 3; //choose SP 
        Mem_CS=0;//enable
        Mem_WR=1;//write
        ARF_RegSel = 6; //only SP
        Reset = 1;
        IR_Enable = 0;
        RF_RegSel = 15; //NO reg enabled
        ALU_FunSel = DecodedALUFunSel; //0000
        ARF_FunSel = 0; //Decrement
    end 
end
endmodule


//Rx<-Value (IM,D)
//decide value according to addressing mode -> into desired reg
module LD(
    input LD, AddressingMode, T2,
    input [1:0] RegSel, //IR[9:8]
    output reg [3:0]RF_RegSel, //RF_TmpSel,
    output reg [1:0]MuxASel, ARF_OutDSel, RF_FunSel, 
    //output reg MemSel, MemStr, MemLd,
    output reg Mem_CS, Mem_WR,
    output reg [2:0]ARF_RegSel,
    output reg Reset, IR_Enable   
);

wire [3:0] decoder_out; 
decoder2to4 decoder2_4(RegSel[1:0], decoder_out);

always@(*) begin
    //direct addressing mode:
    //take the value at the memory from address value in AR
    if(AddressingMode==0)begin
        if(LD&~AddressingMode&T2)begin
            RF_RegSel = ~decoder_out; //R1 or R2 or R3 or R4
            MuxASel=1; //memory output
            ARF_OutDSel=2;//AR
            Mem_CS=0;//enable
            Mem_WR=0;//read
            ARF_RegSel = 7; //none
            Reset =1;
            IR_Enable=0;
            RF_FunSel=2;//load         
        end
    end
    
    //immediate addresing mode
    //get value from Address field(8 bit) of instruction
    else if(AddressingMode)begin
        if(LD&AddressingMode&T2)begin
            RF_RegSel = ~decoder_out; //R1 or R2 or R3 or R4
            MuxASel=0; //IROut(7-0)
            //MemSel =1;
            //MemStr=0;
            //MemLd = 0;
            Mem_CS=0;//enable
            Mem_WR=0;//read?????????
            ARF_RegSel = 7; //none
            Reset =1;
            IR_Enable=0;
            RF_FunSel=2;//load
            //RF_TmpSel=15;//f            
        end
    end
end
endmodule

//value<-Rx (D)
//data in desired reg to address of memory by the address value in AR (Direct addressing)
module ST(
    input ST, AddressingMode, T2,
    input [1:0] RegSel, //IR[9:8]
    input [3:0] DecodedALUFunSel,
    output reg [1:0]RF_OutASel, ARF_OutDSel,
    output reg Mem_CS, Mem_WR,
    output reg [2:0]ARF_RegSel, IR_Enable,
    output reg Reset, MuxCSel,
    output reg [3:0]RF_RegSel,
    output reg [3:0]ALU_FunSel
);

always@(*) begin
    if(AddressingMode==0)begin
        if(ST&~AddressingMode&T2)begin
            RF_OutASel = RegSel; //R1 or R2 or R3 or R4
            MuxCSel=1; //outA //??????
            ARF_OutDSel=2; //AR
            Mem_CS=0;//enable
            Mem_WR=1;//write
            ARF_RegSel = 7; //none
            Reset = 1;
            IR_Enable = 0;
            RF_RegSel = 15; //none
            ALU_FunSel = DecodedALUFunSel; //0000  //give A as output      
        end
    end
    else if(AddressingMode)begin
        if(ST&AddressingMode&T2)begin 
        Reset=1; //turn back to T0
        end
    end
end
endmodule

//Destreg<-Sccreg1 (N/A)
//source reg to dest reg (ARF->ARF,ARF->RF,RF->RF,RF->ARF)
module MOV(  
    input MOV, T2, //????????
    input [3:0] SRCREG1, //IR[7:4] 
    input [3:0] DESTREG, //IR[11:8] 
    input [3:0] DecodedALUFunSel,
    output reg [1:0] MuxBSel, ARF_OutCSel, ARF_FunSel, MuxASel, RF_FunSel, RF_OutASel,
    output reg Mem_CS, Mem_WR,
    output reg [2:0]ARF_RegSel,
    output reg Reset, IR_Enable,
    output reg [3:0]RF_RegSel, /*RF_TmpSel,*/ ALU_FunSel
);

wire [7:0]mux_out1,mux_out2;
MUX4to1 mux_mov1(3,3,5,6,DESTREG[1:0],mux_out1);//????inputlar doru mu++8 bit bu
MUX4to1 mux_mov2(7,11,13,14,DESTREG[1:0],mux_out2);//????inputlar doru mu++8 bit bu
always@(*) begin
    //SRC=ARF DSTR=ARF
    if(SRCREG1[2]==0 & DESTREG[2]==0)begin
        if(MOV & ~SRCREG1 & ~DESTREG & T2)begin
            ARF_OutCSel = SRCREG1[1:0];
            Mem_CS=0;//enable
            Mem_WR=0;//read?????????
            ARF_RegSel = mux_out1[2:0];//??//PC,AR or SP according to destreg(1-0)
            Reset = 1;
            IR_Enable = 0;
            RF_RegSel = 15;//none 
            ARF_FunSel = 2; //load into ARF   
        end
    end
    //SRC=ARF DSTR=RF
    else if(SRCREG1[2]==0 & DESTREG[2]==1)begin
        if(MOV & T2)begin
            MuxASel = 2; //AF outC
            ARF_OutCSel = SRCREG1[1:0];;
            Mem_CS=0;//enable
            Mem_WR=0;//read?????????           
            ARF_RegSel = 7;//none
            Reset = 1;
            IR_Enable = 0;
            RF_RegSel = mux_out2[2:0]; //R1 or R2 or R3 or R4
            RF_FunSel = 2; //load into ARF
        end  
    end    
    //SRC=RF DSTR=RF
    else if(SRCREG1[2]==1 & DESTREG[2]==1)begin
        if(MOV & T2)begin
            MuxASel = 2; //ARF OutC //?
            RF_OutASel = SRCREG1[1:0];
            Mem_CS=0;//enable
            Mem_WR=0;//read?????????            
            ARF_RegSel = 7;//none
            Reset = 1;
            IR_Enable = 0;
            RF_RegSel = mux_out2[3:0];
            RF_FunSel = 2; //load to RF   
            ALU_FunSel = DecodedALUFunSel;           
        end  
    end 
    //SRC=RF DSTR=ARF
    else if(SRCREG1[2]==1 & DESTREG[2]==0)begin
        if(MOV & T2)begin
            //MuxBSel=3; //??BU NOLCAK???????
            RF_OutASel = SRCREG1[1:0];
            Mem_CS=0;//enable
            Mem_WR=0;//read?????????           
            ARF_RegSel = mux_out1[2:0];//Pc, AR or SP
            Reset = 1;
            IR_Enable = 0;
            RF_RegSel = 15;//none
            ARF_FunSel = 2;//load to ARF
            ALU_FunSel = DecodedALUFunSel; //Pass A          
        end  
    end     
end
endmodule
 
//INC = Destreg<-Srcreg1 - 1
//DEC = DEstreg<-Srcreg + 1      
module INC(
    input INC, T2, T3, T4, 
    input [3:0] SRCREG1, //IR[7:4] 
    input [3:0] DESTREG, //IR[11:8] 
    input [3:0] DecodedALUFunSel,
    output reg [1:0] RF_OutASel, MuxASel, MuxBSel, RF_FunSel, RF_OutBSel, ARF_FunSel, ARF_OutCSel, 
    //output reg MemSel, MemStr, MemLd,
    output reg Mem_CS, Mem_WR,
    output reg [2:0]ARF_RegSel,
    output reg Reset, IR_Enable,MuxCSel,
    output reg [3:0]RF_RegSel, //RF_TmpSel,
    output reg [3:0] ALU_FunSel        
);
//inc +1 //dec -1
wire [7:0]mux_out3,mux_out4;
        MUX4to1 mux_mov3(3,3,5,6,DESTREG[1:0],mux_out3);
        MUX4to1 mux_mov4(7,11,13,14,DESTREG[1:0],mux_out4);
        always@(*) begin
        //SCR=RF DST=RF
        if(SRCREG1[2]==1 & DESTREG[2]==1 & T3 & INC)begin
            MuxASel=3;//OutALU
            MuxCSel=1;
            RF_OutASel=SRCREG1[1:0];//source reg
            Mem_CS=0;//enable
            Mem_WR=0;//read???????
            ARF_RegSel=7;
            Reset=1;
            IR_Enable=0;
            RF_RegSel=mux_out4[3:0];//destreg
            RF_FunSel=1;//increment
            ALU_FunSel=DecodedALUFunSel;
        end
        //SCR=RF DST=ARF
        else if(SRCREG1[2]==1 & DESTREG[2]==0 & T3 & INC )begin       
            MuxBSel=3;//??
            MuxCSel=1;
            RF_OutASel=SRCREG1[1:0];
            RF_OutBSel=7;
            Mem_CS=0;//enable
            Mem_WR=0;//read???????            
            ARF_RegSel= mux_out4[2:0];//???
            Reset=1;
            IR_Enable=0;
            ARF_FunSel=1;//increment
            RF_RegSel=15;  
            ALU_FunSel=DecodedALUFunSel;
        end
        //SCR=ARF DST=ARF
        else if(SRCREG1[2]==0 & DESTREG[2]==0 & T4 & INC )begin      
            MuxBSel=3;//??
            MuxCSel=0;
            RF_OutASel = 6;
            RF_OutBSel = 7;
            ARF_RegSel = mux_out3;
            RF_RegSel = 15;
            ARF_FunSel = 1;
            Mem_CS=0;//enable
            Mem_WR=0;//read????
            Reset=1;
            IR_Enable=0;
            ALU_FunSel = DecodedALUFunSel;
        end
        //SCR=ARF DST=RF
         else if(SRCREG1[2]==0 & DESTREG[2]==1 & T4 & INC )begin      
           MuxASel=2;//??
           MuxCSel=0;
           RF_OutASel = 6;
           RF_OutBSel = 7;
           ARF_RegSel = 7;
           RF_RegSel = mux_out4;
           RF_FunSel = 1;
           Mem_CS=0;//enable
           Mem_WR=0;//read????
           Reset=1;
           IR_Enable=0;
           ALU_FunSel = DecodedALUFunSel;
       end  
    end
endmodule

module DEC(
    input DEC, T2, T3, T4,
    input [3:0] SRCREG1, //IR[7:4] 
    input [3:0] DESTREG, //IR[11:8] 
    input [3:0] DecodedALUFunSel,
    output reg [1:0] RF_OutASel, MuxASel, MuxBSel, RF_FunSel, RF_OutBSel, ARF_FunSel, ARF_OutCSel, 
    output reg Mem_CS, Mem_WR,
    output reg [2:0]ARF_RegSel,
    output reg Reset, IR_Enable,MuxCSel,
    output reg [3:0]RF_RegSel, //RF_TmpSel,
    output reg [3:0] ALU_FunSel        
);
//inc +1 //dec -1
wire [7:0]mux_out3,mux_out4;
        MUX4to1 mux_mov3(3,3,5,6,DESTREG[1:0],mux_out3);
        MUX4to1 mux_mov4(7,11,13,14,DESTREG[1:0],mux_out4);
        always@(*) begin
        //SCR=RF DST=RF
        if(SRCREG1[2]==1 & DESTREG[2]==1  & T3 & DEC)begin
            MuxASel=3;//OutALU
            MuxCSel=1;
            RF_OutASel=SRCREG1[1:0];//source reg
            RF_OutBSel=7;
            Mem_CS=0;//enable
            Mem_WR=0;//read????
            ARF_RegSel=7;
            Reset=1;
            IR_Enable=0;
            //RF_TmpSel=15;
            RF_RegSel=mux_out4[3:0];//destreg
            RF_FunSel=0;//decrement
            ALU_FunSel=DecodedALUFunSel;
        end
        //SCR=RF DST=ARF
        else if(SRCREG1[2]==1 & DESTREG[2]==0  & T3 & DEC )begin       
            MuxBSel=3;//??
            MuxCSel=1;
            RF_OutASel=SRCREG1[1:0];
            RF_OutBSel=7;
            Mem_CS=0;//enable
            Mem_WR=0;//read????
            ARF_RegSel= mux_out4[2:0];//???
            Reset=1;
            IR_Enable=0;
            ARF_FunSel=0;//decrement   
            RF_RegSel=15;  
            ALU_FunSel=DecodedALUFunSel;
        end
        //SCR=ARF DST=ARF
        else if(SRCREG1[2]==0 & DESTREG[2]==0  & T4 & DEC )begin      
            MuxBSel=3;//??
            MuxCSel=0;
            RF_OutASel = 6;
            RF_OutBSel = 7;
            ARF_RegSel = mux_out3;
            RF_RegSel = 15;
            ARF_FunSel = 0;
            Mem_CS=0;//enable
            Mem_WR=0;//read????
            Reset=1;
            IR_Enable=0;
            ALU_FunSel = DecodedALUFunSel;
        end
        //SCR=ARF DST=RF
         else if(SRCREG1[2]==0 & DESTREG[2]==1  & T4 & DEC )begin      
           MuxASel=2;//??
           MuxCSel=0;
           RF_OutASel = 6;
           RF_OutBSel = 7;
           ARF_RegSel = 7;
           RF_RegSel = mux_out4;
           RF_FunSel = 0;
           Mem_CS=0;//enable
           Mem_WR=0;//read????
           Reset=1;
           IR_Enable=0;
           ALU_FunSel = DecodedALUFunSel;
       end  
    end
endmodule

module NOT_LSL_LSR(
    input NOT, LSL, LSR,
    input [0:0] T2, T3,
    input [3:0] SRCREG1,
    input [3:0] DESTREG,
    output reg [1:0]MuxASel, ARF_OutCSel, MuxBSel, RF_OutASel,
    output reg Mem_CS, Mem_WR,
    output reg Dec_ALU_FunSel, RF_FunSel, ARF_FunSel,
    output reg [2:0]ARF_RegSel,
    output reg [0:0] Reset, IR_Enable,
    output reg [3:0] RF_RegSel, ALU_FunSel
    );
wire or_out;
assign or_out = NOT | LSL | LSR;
wire mux_out1, mux_out2, mux_out3, mux_out4;
MUX4to1 mux1(3, 3, 5, 6, DESTREG[1:0], mux_out1);
MUX4to1 mux2(7, 11, 13, 14, DESTREG[1:0], mux_out2);
MUX4to1 mux3(3, 3, 5, 6, DESTREG[1:0], mux_out3);
MUX4to1 mux4(7, 11, 13, 14, DESTREG[1:0], mux_out4);
always @(*) begin
    if(or_out & SRCREG1[2]==0 & T2) begin
        MuxASel = 3;
        ARF_OutCSel = SRCREG1;
        Mem_CS=0;
        Mem_WR=0;
        ARF_RegSel = 7;
        Reset = 0;
        IR_Enable = 0;
        RF_RegSel = 7;
        RF_FunSel = 2;
    end
    else if(or_out & SRCREG1[2]==0 & DESTREG[2]==0 & T3) begin
        MuxBSel = 0;
        RF_OutASel = 4;
        Mem_CS=0;
        Mem_WR=0;
        ARF_RegSel = mux_out1;
        Reset = 1;
        IR_Enable = 0;
        RF_RegSel = 15;
        ARF_FunSel = 2;
        ALU_FunSel = Dec_ALU_FunSel;
    end
    else if(or_out & SRCREG1[2]==0 & DESTREG[2]==1 & T3) begin
        MuxASel = 0;
        RF_OutASel = 4;
        Mem_CS=0;
        Mem_WR=0;
        ARF_RegSel = 7;
        Reset = 1;
        IR_Enable = 0;
        RF_RegSel = mux_out2;
        ARF_FunSel = 2;
        ALU_FunSel = Dec_ALU_FunSel;
    end
    else if(or_out & SRCREG1[2]==1 & DESTREG[2]==0 & T2) begin
        MuxBSel = 0;
        RF_OutASel = SRCREG1[1:0];
        Mem_CS=0;
        Mem_WR=0;
        ARF_RegSel = mux_out3;
        Reset = 1;
        IR_Enable = 0;
        RF_RegSel = 15;
        ARF_FunSel = 2;
        ALU_FunSel = Dec_ALU_FunSel;
    end
    else if(or_out & SRCREG1[2]==1 & DESTREG[2]==1 & T2) begin
        MuxASel = 0;
        RF_OutASel = SRCREG1[1:0];
        Mem_CS=0;
        Mem_WR=0;
        ARF_RegSel = 7;
        Reset = 1;
        IR_Enable = 0;
        RF_RegSel = mux_out4;
        RF_FunSel = 2;
        ALU_FunSel = Dec_ALU_FunSel;
    end
end
endmodule
    
module AND_OR_ADD_SUB(
            input AND, OR, ADD, SUB,
            input T2,T3,
            input [3:0] SRCREG1, //IR[7:4] 
            input [3:0] SRCREG2, //IR[7:4] 
            input [3:0] DESTREG, //IR[11:8] 
            input [3:0] DecodedALUFunSel,
            output reg [3:0] ALU_FunSel,
            output reg [1:0] ARF_FunSel,
            output reg [3:0] RF_RegSel,
            output reg IR_Enable,
            output reg Reset,
            output reg [2:0] ARF_RegSel,
            output reg Mem_CS, Mem_WR,
            output reg [1:0]RF_OutASel,
            output reg [1:0]RF_OutBSel,
            output reg [1:0]ARF_OutCSel,
            output reg [1:0]MuxBSel,
            output reg [1:0]MuxASel,
            output reg [1:0]RF_FunSel
        );
        wire [7:0]mux_out1, mux_out2;
        MUX4to1 mux_mov1(3,3,5,6,DESTREG[1:0],mux_out1);
        MUX4to1 mux_mov2(7,11,13,14,DESTREG[1:0],mux_out2);
        
        always@(*) begin
            if((AND | OR | ADD | SUB) & SRCREG1[2]==1 & SRCREG2[2]==1 & DESTREG[2]==0 & T2)begin
                RF_OutBSel = SRCREG1[1:0];
                MuxBSel =0;
                RF_OutASel = SRCREG2[1:0];              
                Mem_CS=0;
                Mem_WR=0;
                ARF_RegSel = mux_out1;
                Reset =0;
                IR_Enable =0;
                RF_RegSel = 15;               
                ARF_FunSel = 2;
                ALU_FunSel = DecodedALUFunSel;
            end
            else if((AND | OR | ADD | SUB) & SRCREG1[2]==1 & SRCREG2[2]==1 & DESTREG[2]==1 & T2)begin
                MuxASel =0;
                RF_OutBSel = SRCREG1[1:0];
                RF_OutASel = SRCREG2[1:0];
                Mem_CS=0;
                Mem_WR=0;
                ARF_RegSel = 7;
                Reset =1;
                IR_Enable =0;
                RF_RegSel = mux_out2;
                RF_FunSel =2;
                ALU_FunSel = DecodedALUFunSel;         
            end
            
            else if((AND | OR | ADD | SUB) & SRCREG1[2]==0 & SRCREG2[2]==1 & T2)begin
                ARF_OutCSel = SRCREG1[1:0];
                MuxASel =3;
                RF_OutASel =5;
                Mem_CS=0;
                Mem_WR=0;
                ARF_RegSel = 7;
                Reset =0;
                IR_Enable =0;
                RF_RegSel = 15;
                RF_FunSel =2;
            end
            
            else if((AND | OR | ADD | SUB) & SRCREG1[2]==0 & SRCREG2[2]==1 & DESTREG[2]==1 & T3)begin
                RF_OutBSel = 4;
                MuxASel =3;
                RF_OutASel =SRCREG2[1:0];
                Mem_CS=0;
                Mem_WR=0;
                ARF_RegSel = 7;
                Reset =1;
                IR_Enable =0;
                RF_RegSel = mux_out2;
                RF_FunSel =2;
                ALU_FunSel = DecodedALUFunSel;            
            end
            else if((AND | OR | ADD | SUB) & SRCREG1[2]==0 & SRCREG2[2]==1 & DESTREG[2]==0 & T3)begin
                RF_OutBSel = 4;
                MuxBSel =0;
                RF_OutASel =SRCREG2[1:0];               
                Mem_CS=0;
                Mem_WR=0;
                ARF_RegSel = mux_out1;
                Reset =1;
                IR_Enable =0;
                RF_RegSel =15;
                RF_FunSel =2;
                ALU_FunSel = DecodedALUFunSel;            
            end      
        end
        endmodule

module PUL(
            input PUL,
            input [0:0]T2, [0:0]T3,
            input [3:0] DESTREG,
            output reg [2:0]ARF_RegSel,
            output reg [1:0]ARF_FunSel, RF_FunSel,
            output reg [0:0]Reset,
            output reg [3:0]RF_RegSel,
            output reg Mem_CS, Mem_WR,
            output reg IR_Enable, OutDSel, MUXASel
            );
        wire [3:0] decoder_out, decoder_out_not;
        decoder2to4 dec(DESTREG[1:0], decoder_out);
        assign decoder_out_not = ~decoder_out;
        always@(*) begin
            if(PUL & T2) begin
                ARF_RegSel = 6;
                ARF_FunSel = 1;
                Mem_CS=0;
                Mem_WR=0;
                Reset = 0;
                IR_Enable = 0;
                RF_RegSel = 15;
            end
            else if(PUL & T3) begin
                RF_RegSel = decoder_out_not;
                RF_FunSel = 2;
                ARF_RegSel = 7;
                OutDSel = 3;
                Mem_CS=0;
                Mem_WR=0;
                MUXASel = 1;
                Reset = 1;
                IR_Enable = 0; 
            end
        end
        endmodule


module System(
    input Reset, clock,   
    output wire T0, T1, T2, T3, T4, T5, T6, T7
    );
    wire MuxCSel;
    wire IR_Enable, IR_LH;
    wire [1:0]MuxASel, MuxBSel, RF_FunSel, ARF_FunSel, IR_Funsel;
    wire [2:0] ARF_RegSel;
    wire [1:0]ARF_OutCSel, ARF_OutDSel, RF_OutASel,RF_OutBSel;
    wire [3:0]RF_RegSel, ALU_FunSel;
    wire Mem_WR, Mem_CS;
    
    wire AOut, BOut, ALUOut, MemoryOut, MuxAOut, MuxBOut, MuxCOut, ALUOutFlag, IROut, ARF_COut;

    wire AddressingMode,  Z, BNE ,BRA;
    wire PSH;
    wire [3:0]DESTREG;
    wire [3:0] SRCREG1; //IR[7:4] 
    wire [3:0] SRCREG2; //IR[7:4] 
    wire [3:0]DecodedALUFunSel;
    wire PUL;
    wire OutDSel;
    wire LD;
    wire [1:0] RegSel;
    wire ST; 
    wire MOV;
    wire NOT, LSL, LSR;
    wire INC, DEC, AND, OR, ADD, SUB;
    wire [3:0]OPCODE; 
    wire [7:0]Address;
SequentialCounter seq2(Reset, clock, T0, T1, T2, T3, T4, T5, T6, T7);

Fetch fetch(T0, T1, ARF_OutDSel, ARF_FunSel, IR_Funsel, ARF_RegSel, Mem_WR, Mem_CS, IR_Enable, IR_LH, Reset, RF_RegSel);

Decode decode(IROut, Address, RegSel, AddressingMode, OPCODE, SRCREG2, SRCREG1, DESTREG, BRA, LD, ST, MOV, AND, OR, NOT, ADD, SUB, LSL, LSR, PUL, PSH, INC, DEC, BNE, DecodedALUFunSel);
ALUSystem part4(IR_LH, IR_Enable, MuxASel, MuxBSel,MuxCSel, RF_FunSel, ARF_FunSel, IR_Funsel,
                ARF_OutCSel, ARF_OutDSel, ARF_RegSel,RF_OutASel,RF_OutBSel, RF_RegSel,ALU_FunSel,
                Mem_WR, Mem_CS, clock, AOut, BOut, ALUOut, Address, MemoryOut, MuxAOut, MuxBOut, MuxCOut, ALUOutFlag, IROut, ARF_COut);
BRA bra(BRA, AddressingMode, T2, IR_Enable, Reset, MuxBSel, ARF_FunSel, ARF_RegSel, Mem_CS, Mem_WR, RF_RegSel);
BNE bne(AddressingMode, T2, Z, BNE, IR_Enable, Reset, MuxBSel, ARF_FunSel, ARF_RegSel, Mem_CS, Mem_WR, RF_RegSel);
PSH psh(PSH,T2,DESTREG,DecodedALUFunSel,RF_OutASel,ARF_OutDSel, Mem_CS, Mem_WR, ARF_RegSel,Reset, IR_Enable, MuxCSel,RF_RegSel, ALU_FunSel,ARF_FunSel);  
PUL pul(PUL,T2,T3,DESTREG,ARF_RegSel,ARF_FunSel, RF_FunSel,Reset,RF_RegSel, Mem_CS, Mem_WR, IR_Enable, OutDSel, MuxASel);         
LD ld(LD,AddressingMode, T2, RegSel,RF_RegSel, MuxASel, ARF_OutDSel, RF_FunSel, Mem_CS, Mem_WR, ARF_RegSel, Reset, IR_Enable) ;             
ST st(ST, AddressingMode, T2, RegSel, DecodedALUFunSel, RF_OutASel, ARF_OutDSel, Mem_CS, Mem_WR, ARF_RegSel, IR_Enable, Reset, MuxCSel, RF_RegSel, ALU_FunSel); 
MOV mov(MOV, T2, SRCREG1, DESTREG,DecodedALUFunSel,MuxBSel, ARF_OutCSel, ARF_FunSel, MuxASel, RF_FunSel, RF_OutASel, Mem_CS, Mem_WR,ARF_RegSel,Reset, IR_Enable,RF_RegSel, ALU_FunSel);           
NOT_LSL_LSR not_lsl_lsr(NOT, LSL, LSR, SRCREG1, DESTREG,T2, T3,  MuxASel, ARF_OutCSel, MuxBSel, RF_OutASel, Mem_CS, Mem_WR, RF_FunSel, ARF_FunSel, DecodedALUFunSel ,ARF_RegSel, Reset, IR_Enable, RF_RegSel, ALU_FunSel);
INC inc( INC, T2, T3, T4, SRCREG1, DESTREG, DecodedALUFunSel, RF_OutASel, MuxASel, MuxBSel, RF_FunSel, RF_OutBSel, ARF_FunSel, ARF_OutCSel,Mem_CS, Mem_WR, ARF_RegSel,Reset, IR_Enable,RF_RegSel, RF_RegSel, ALU_FunSel);
DEC dec( DEC, T2, T3, T4,  SRCREG1, DESTREG, DecodedALUFunSel, RF_OutASel, MuxASel, MuxBSel, RF_FunSel, RF_OutBSel, ARF_FunSel, ARF_OutCSel,Mem_CS, Mem_WR, ARF_RegSel,Reset, IR_Enable,RF_RegSel, RF_RegSel, ALU_FunSel);
AND_OR_ADD_SUB and_or_add_sub(AND, OR, ADD, SUB, T2,T3,  SRCREG1,SRCREG2, DESTREG, DecodedALUFunSel, ALU_FunSel, ARF_FunSel,RF_RegSel, IR_Enable,Reset,ARF_RegSel, Mem_CS, Mem_WR, RF_OutASel,RF_OutBSel,ARF_OutCSel,MuxBSel,MuxASel,RF_FunSel);

endmodule


        

