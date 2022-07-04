`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: ÝTÜ
// Engineer: Aybike Zeynep Taþkýn 150190004 Feray Lina Yence 150190007 Mevlüt Erdoðdu 150180051
// Create Date: 08.05.2022 15:14:53
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


module Simulations();
endmodule

module Project1Test();
    //Input Registers of ALUSystem
    reg[1:0] RF_OutASel; 
    reg[1:0] RF_OutBSel; 
    reg[1:0] RF_FunSel;
    reg[3:0] RF_RegSel;
    reg[3:0] ALU_FunSel;
    reg[1:0] ARF_OutCSel; 
    reg[1:0] ARF_OutDSel; 
    reg[1:0] ARF_FunSel;
    reg[2:0] ARF_RegSel;
    reg      IR_LH;
    reg      IR_Enable;
    reg[1:0]      IR_Funsel;
    reg      Mem_WR;
    reg      Mem_CS;
    reg[1:0] MuxASel;
    reg[1:0] MuxBSel;
    reg MuxCSel;
    reg      Clock;
    
    //Test Bench Connection of ALU System
    ALUSystem _ALUSystem(
    .RF_OutASel(RF_OutASel), 
    .RF_OutBSel(RF_OutBSel), 
    .RF_FunSel(RF_FunSel),
    .RF_RegSel(RF_RegSel),
    .ALU_FunSel(ALU_FunSel),
    .ARF_OutCSel(ARF_OutCSel), 
    .ARF_OutDSel(ARF_OutDSel), 
    .ARF_FunSel(ARF_FunSel),
    .ARF_RegSel(ARF_RegSel),
    .IR_LH(IR_LH),
    .IR_Enable(IR_Enable),
    .IR_Funsel(IR_Funsel),
    .Mem_WR(Mem_WR),
    .Mem_CS(Mem_CS),
    .MuxASel(MuxASel),
    .MuxBSel(MuxBSel),
    .MuxCSel(MuxCSel),
    .Clock(Clock)
    );
    
    //Test Vector Variables
    reg [31:0] VectorNum, Errors, TotalLine; 
    reg [34:0] TestVectors[10000:0];
    reg Reset, Operation;
    
    //Clock Signal Generation
    always 
    begin
        Clock = 1; #5; Clock = 0; #5; // 10ns period
    end
    
    //Read Test Bench Values
    initial begin
        $readmemb("TestBench.mem", TestVectors); // Read vectors
        VectorNum = 0; Errors = 0; TotalLine=0; Reset=0;// Initialize
    end
    
    // Apply test vectors on rising edge of clock
    always @(posedge Clock)
    begin
        #1; 
        {Operation, RF_OutASel, RF_OutBSel, RF_FunSel, 
        RF_RegSel, ALU_FunSel, ARF_OutCSel, ARF_OutDSel, 
        ARF_FunSel, ARF_RegSel, IR_LH, IR_Enable, IR_Funsel, 
        Mem_WR, Mem_CS, MuxASel, MuxBSel, MuxCSel} = TestVectors[VectorNum];
    end
    
    // Check results on falling edge of clk
    always @(negedge Clock)
        if (~Reset) // skip during reset
        begin
            $display("Input Values:");
            $display("Operation: %d", Operation);
            $display("Register File: OutASel: %d, OutBSel: %d, FunSel: %d, Regsel: %d", RF_OutASel, RF_OutBSel, RF_FunSel, RF_RegSel);            
            $display("ALU FunSel: %d", ALU_FunSel);
            $display("Addres Register File: OutCSel: %d, OutDSel: %d, FunSel: %d, Regsel: %d", ARF_OutCSel, ARF_OutDSel, ARF_FunSel, ARF_RegSel);            
            $display("Instruction Register: LH: %d, Enable: %d, FunSel: %d", IR_LH, IR_Enable, IR_Funsel);            
            $display("Memory: WR: %d, CS: %d", Mem_WR, Mem_CS);
            $display("MuxASel: %d, MuxBSel: %d, MuxCSel: %d", MuxASel, MuxBSel, MuxCSel);
            
            $display("");
            $display("Ouput Values:");
            $display("Register File: AOut: %d, BOut: %d", _ALUSystem.AOut, _ALUSystem.BOut);            
            $display("ALUOut: %d, ALUOutFlag: %d, ALUOutFlags: Z:%d, C:%d, N:%d, O:%d,", _ALUSystem.ALUOut, _ALUSystem.ALUOutFlag, _ALUSystem.ALUOutFlag[3],_ALUSystem.ALUOutFlag[2],_ALUSystem.ALUOutFlag[1],_ALUSystem.ALUOutFlag[0]);
            $display("Address Register File: COut: %d, DOut (Address): %d", _ALUSystem.ARF_COut, _ALUSystem.Address);            
            $display("Memory Out: %d", _ALUSystem.MemoryOut);            
            $display("Instruction Register: IROut: %d", _ALUSystem.IROut);            
            $display("MuxAOut: %d, MuxBOut: %d, MuxCOut: %d", _ALUSystem.MuxAOut, _ALUSystem.MuxBOut, _ALUSystem.MuxCOut);
            
            // increment array index and read next testvector
            VectorNum = VectorNum + 1;
            if (TestVectors[VectorNum] === 35'bx)
            begin
                $display("%d tests completed.",
                VectorNum);
                $finish; // End simulation
            end
        end
endmodule


module eight_bit_register_test();
    reg [7:0] I;
    reg enable, clk;
    reg [1:0] FunSel;
    wire [7:0] reg_out;
    eight_bit_register uut(I, enable, FunSel, clk, reg_out); // reg_out_7, reg_out_6,reg_out_5, reg_out_4, reg_out_3, reg_out_2, reg_out_1, reg_out_0);
    initial begin
           clk=0;
            forever #50 clk = ~clk;
       end
    initial begin
        I = 11010011; enable = 1;   FunSel = 10; # 100;//11010011
        I = 11010011; enable = 0;   FunSel = 11; # 100;//11010011
        I = 11010011; enable = 0;   FunSel = 11; # 100;//11010011
        I = 11010011; enable = 1;   FunSel = 11; # 100;//00000000  
        I = 11111111; enable = 1;   FunSel = 10; # 100;//11111111   
        I = 00000001; enable = 1; FunSel = 01; # 100;//11110001
        I = 00000001; enable = 1;  FunSel = 01; # 100;//11110010
        I = 00000001; enable = 1;  FunSel = 00; # 100;//11110001
        I = 00000001; enable = 1;  FunSel = 00; # 100;//11110000 
        I = 11010011; enable = 1;   FunSel = 11; # 100;
     end
endmodule


module sixteen_bit_register_test();
    reg [15:0] I;
    reg enable;
    reg [1:0] FunSel;
    reg clk;
    wire [15:0] reg_out;
    sixteen_bit_register uut(I, enable, FunSel, clk, reg_out); 
    initial begin
           clk=0;
            forever #20 clk = ~clk;
       end
    initial begin
        I = 16'b1111111111010011; enable = 1;   FunSel = 11; # 100;
        I = 16'b1111111111010011; enable = 0;   FunSel = 10; # 100;
        I = 16'b1111111111010011; enable = 1;   FunSel = 10; # 100;    
        I = 16'b0000000000000001; enable = 1;  FunSel = 00; # 100;   
        I = 16'b1111111111010011; enable = 1;   FunSel = 11; # 100;         
        I = 16'b0000000000001111; enable = 1;  FunSel = 01; # 100;
        I = 16'b0000000000001111; enable = 1; FunSel = 00; # 100;
        I = 16'b1111111111010011; enable = 1;   FunSel = 11; # 100;
        I = 16'b0000000000000001; enable = 1; FunSel = 00; # 100;
        I = 16'b0000000000001111; enable = 1;  FunSel = 01; # 100;
     end
endmodule


module address_register_test();
    reg [7:0] I;
    reg [1:0] FunSel;
    reg clk;
    reg [2:0] RegSel;
    reg [1:0] OutCSel;
    reg [1:0] OutDSel;
    wire [7:0] OutC;
    wire [7:0] OutD;
    address_register uut(I,FunSel, clk, RegSel, OutCSel, OutDSel, OutC, OutD);
    initial begin
           clk=0;
            forever #25 clk = ~clk;
       end
    initial begin
        I = 00000001;     FunSel = 11; RegSel = 3'b000;  OutCSel = 00;  OutDSel = 0000; # 100;
        I = 00000001;     FunSel = 10; RegSel = 3'b011;  OutCSel = 00;  OutDSel = 0000; # 100;
        I = 00000010;     FunSel = 10; RegSel = 3'b101;  OutCSel = 00;  OutDSel = 0000; # 100;
        I = 00000100;     FunSel = 10; RegSel = 3'b110;  OutCSel = 00;  OutDSel = 0000; # 100;
        I = 00000001;     FunSel = 00; RegSel = 3'b110;  OutCSel = 00;  OutDSel = 0000; # 100;
        I = 00000010;     FunSel = 00; RegSel = 3'b101;  OutCSel = 00;  OutDSel = 0000; # 100;
        I = 00000100;    FunSel = 00; RegSel = 3'b011;  OutCSel = 00;  OutDSel = 0000; # 100;
        I = 00000001;    FunSel = 11; RegSel = 3'b000;  OutCSel = 00;  OutDSel = 0000; # 100;
        I = 11010011;    FunSel = 10; RegSel = 3'b000; OutCSel = 01; OutDSel = 0001; # 100;
        I = 11010011;     FunSel = 10; RegSel = 3'b000; OutCSel = 10; OutDSel = 0010; # 100;
        I = 11010011;     FunSel = 10; RegSel = 3'b000;  OutCSel = 11;  OutDSel = 0011; # 100;
     end
endmodule

module Part2A_test();
    reg [7:0] I;
    reg [1:0] outASel;
    reg [1:0] outBSel;
    reg [1:0] FunSel;
    reg [3:0] RegSel;
    reg [0:0] clock;
    wire [7:0] outAData;
    wire [7:0] outBData;
    Part2A uut(I, outASel, outBSel, FunSel, RegSel, clock, outAData, outBData);
     initial begin
              clock=0;
               forever #20 clock = ~clock;
          end
           initial begin
              I = 00000001;     FunSel = 11; RegSel = 3'b000;  outASel = 00;  outBSel = 00; # 100;
              I = 00000001;     FunSel = 10; RegSel = 3'b011;  outASel = 00;  outBSel = 00; # 100;
              I = 00000010;     FunSel = 10; RegSel = 3'b101;  outASel = 00;  outBSel = 00; # 100;
              I = 00000100;     FunSel = 10; RegSel = 3'b110;  outASel = 00;  outBSel = 00; # 100;
              I = 00000001;     FunSel = 00; RegSel = 3'b110;  outASel = 00;  outBSel = 11; # 100;
              I = 00000010;     FunSel = 00; RegSel = 3'b101;  outASel = 00;  outBSel = 10; # 100;
              I = 00000100;    FunSel = 00; RegSel = 3'b011;  outASel = 00;  outBSel = 01; # 100;
              I = 00000001;    FunSel = 11; RegSel = 3'b000;  outASel = 10;  outBSel = 01; # 100;
              I = 11010011;    FunSel = 10; RegSel = 3'b000; outASel = 01;   outBSel = 01; # 100;
              I = 11010011;     FunSel = 10; RegSel = 3'b000; outASel = 11;  outBSel = 10; # 100;
              I = 11010011;     FunSel = 10; RegSel = 3'b000;  outASel = 11;  outBSel = 11; # 100;
           end
endmodule

module MUX4to1_test();
    reg in0, in1 ,in2, in3;
    reg [1:0]FunSel;
    wire out;

    MUX4to1 uut(.in0(in0), .in1(in1), .in2(in2), .in3(in3), .FunSel(FunSel), .out(out));
    
    initial begin
        in0 = 1; in1 = 0; in2 = 0; in3 = 0; FunSel= 0;  #100;       
        in0 = 0; in1 = 0; in2 = 0; in3 = 0; FunSel= 1;  #100;
        in0 = 0; in1 = 0; in2 = 0; in3 = 0; FunSel= 1; #100;
        in0 = 0; in1 = 0; in2 = 0; in3 = 1; FunSel= 2; #100;
        in0 = 0; in1 = 0; in2 = 0; in3 = 1; FunSel= 3;  #100;
    end
endmodule

module not_gate_test();
    reg a;
    
    wire o;
    
    not_gate uut(a, o);
    
    initial begin
        a = 0;  #250;
        a = 1;  #250;
    end
endmodule

module Part_two_C_test();
   reg [7:0] I;
   reg enable;
   reg [1:0] FunSel;
   reg clk, LH;
   wire [15:0] reg_out;
   Part_two_C uut(I, enable, FunSel, clk, LH,  reg_out); 
   initial begin
          clk=0;
           forever #20 clk = ~clk;
      end
   initial begin
       I = 8'b11010011; enable = 1;   LH = 0; FunSel = 11; # 100;//clear
       I = 8'b11010011; enable = 0;   LH = 0; FunSel = 01; # 100;
       I = 8'b11010011; enable = 1;   LH = 0; FunSel = 01; # 100;//increment
       I = 8'b11010011; enable = 1;   LH = 0; FunSel = 00; # 100;//decrement
       I = 8'b11110000; enable = 1;   LH = 0 ; FunSel = 10; # 100; //load to msb
       I = 8'b00001111; enable = 1;   LH = 1 ; FunSel = 10; # 100; //load to lsb
       I = 8'b11010011; enable = 1;  LH = 0; FunSel = 11; # 100;//clear
       I = 8'b10101010; enable = 1;   LH = 1; FunSel = 10; # 100;//load to lsb
       I = 8'b10101010; enable = 1;   LH = 0; FunSel = 10; # 100;//load to msb
    end
endmodule


module MUX2to1_test();
    reg in0, in1;
    reg LH;
    wire out;

    MUX2to1 uut(.in0(in0), .in1(in1), .LH(LH), .out(out));
    
    initial begin
        in0 = 1; in1 = 0;  LH= 0; #100; 
        in0 = 0; in1 = 1;  LH= 0; #100;        
        in0 = 0; in1 = 0;  LH= 1; #100;
        in0 = 0; in1 = 1;  LH= 1; #100;
        in0 = 0; in1 = 1;  LH= 1; #100;
        in0 = 0; in1 = 0;  LH= 1; #100;
       
    end
endmodule

module alu_test();
    reg [7:0] A;
    reg [7:0] B;
    reg [3:0] FunSel;
    reg c_in;
    reg [0:0]clk;
    wire [7:0] OutALU;
    wire [3:0] flag_out;
    ALU_Part3 uut(A, B, FunSel, c_in, clk, OutALU, flag_out);
    initial begin
       clk=0;
       forever #20 clk = ~clk;
    end
    initial begin
        A = 00000000; B = 01010101; FunSel = 00; c_in = 0; #50;
        A = 00000000; B = 01010101; FunSel = 00; c_in = 1; #50;
        A = 00000000; B = 01010101; FunSel = 01; c_in = 0; #50;
        A = 00000000; B = 01010101; FunSel = 01; c_in = 1; #50;
        A = 00000000; B = 01010101; FunSel = 10; c_in = 0; #50;
        A = 00000000; B = 01010101; FunSel = 10; c_in = 1; #50;
        A = 00000000; B = 01010101; FunSel = 11; c_in = 0; #50;
        A = 00000000; B = 01010101; FunSel = 11; c_in = 1; #50;
    end
endmodule

module SequentialCounter_test();
    reg reset;
    reg clk;
    wire T0, T1, T2, T3, T4, T5, T6, T7;
    
    SequentialCounter uut(reset, clk, T0, T1, T2, T3, T4, T5, T6, T7);
     initial begin
          clk=0;
          forever #20 clk = ~clk;
       end
       initial begin
            reset = 0; #50;//increment
            reset = 1; #50;//clear
            reset = 0; #50;//increment
            reset = 0; #50;//increment
            reset = 0; #50;//increment
            reset = 0; #50;//increment
            reset = 1; #50;//clear
            reset = 1; #50;//clear
            reset = 0; #50;//increment
            reset = 0; #50;//increment
            reset = 0; #50;//increment
            reset = 0; #50;//increment
            reset = 0; #50;//increment
            reset = 1; #50;//clear
       end
endmodule

module System_test();
    reg reset,clock;
    wire T0, T1, T2, T3, T4, T5, T6, T7;
    System uut(reset,clock,T0, T1, T2, T3, T4, T5, T6, T7);
     initial begin
         clock=0;
         forever #20 clock = ~clock;
      end
      initial begin
           reset = 1; #100;
           reset = 0; #100;
           reset = 0; #100;
           reset = 0; #100;
           reset = 0; #100;
           reset = 0; #100;
           reset = 0; #100;
           reset = 0; #100;
           reset = 1; #100;
      end
endmodule    

   
