
`timescale 1ns/100ps

   `define ADD  3'b000
   `define SUB  3'b001
   `define SLT  3'b010
   `define SLTU 3'b011
   `define AND  3'b100
   `define XOR  3'b101
   `define OR   3'b110
   `define NOR  3'b111

module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR ,HI, LO;

   // Data Path Control Lines, don't forget, regs are not always register !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, RFwrt, IRwrt, MDRwrt, MARwrt;
   reg multStart;
   reg [1:0] PCwrt; // modified for jump instructions

   // Memory Ports Bindings
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Line
   reg [2:0] aluOp;
   reg [2:0] aluSelB;
   reg SgnExt, aluSelA, RegDst, IorD;
   reg [2:0] MemtoReg;
   reg JAL;

   // Wiring
   wire aluZero;
   wire multReady;
   wire [31:0] aluResult, rfRD1, rfRD2;
   wire [31:0] lo, hi;

   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt == 2'b01 )
         PC <= #0.1 aluResult;
      else if( PCwrt == 2'b10 )
         PC <= #0.1 A;
      else if( PCwrt == 2'b11 )
         PC <= #0.1 {PC[31:28],IR[25:0],2'b00};

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? aluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;

   end

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      .WR( JAL ? 5'b11111 : RegDst ? IR[15:11] : IR[20:16] ),
      .WD( (MemtoReg == 3'b001) ? MDR : (MemtoReg == 3'b000) ? aluResult : (MemtoReg == 3'b010) ? {IR[15:0],16'h0000} : (MemtoReg == 3'b011) ? HI : LO)
   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};

   // ALU-A Mux
   wire [31:0] aluA = aluSelA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
      3'b000: aluB = B;
      3'b001: aluB = 32'h4;
      3'b010: aluB = SZout;
      3'b011: aluB = SZout << 2;
      3'b100: aluB = 0;
   endcase

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),

      .X( aluResult ),
      .Z( aluZero )
   );

   // Multiplier

   multiplier mult(
      .clk(clk),
      .start(multStart),
      .A(A),
      .B(B),
      .lower(lo),
      .higher(hi),
      .ready(multReady)
   );

   always@(*) begin
      if(multReady) begin
         LO = lo;
         HI = hi;
      end
   end

   // Controller Starts Here

   // Controller State Registers
   reg [4:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_JR = 5 , EX_JALR = 6,
      EX_ALU_R = 7, EX_ALU_I = 8, EX_J = 9, EX_LUI = 10,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_MULT_1 = 16, EX_MULT_2 = 17, EX_BRA_1 = 19, EX_BRA_2 = 20,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23, EX_MFX = 24;
      
   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;

      PCwrt = 2'b00;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;
      multStart = 0;
      JAL = 0;

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 2'b01;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 3'b001;
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b000: ;
                     3'b001: nxt_state = (IR[2:0]==3'b000) ? EX_JR : EX_JALR;
                     3'b010: nxt_state = EX_MFX;
                     3'b011: nxt_state = EX_MULT_1;
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                     3'b110: ;
                     3'b111: ;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110:             // xori
                  nxt_state = EX_ALU_I;

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100,
               6'b000_101:
                  nxt_state = EX_BRA_1;
               
               // rest of instructiones should be decoded here

               6'b000_010,
               6'b000_011:
                  nxt_state = EX_J;

               6'b001_111:
                  nxt_state = EX_LUI;

            endcase
         end

         EX_ALU_R: begin
            RegDst = 1'b1;
            MemtoReg = 3'b000;
            aluSelA = 1'b1;
            aluSelB = 3'b000;
            RFwrt = 1'b1;

            case(IR[5:0])
               6'b100000,
               6'b100001: aluOp = `ADD ;
               6'b100010,
               6'b100011: aluOp = `SUB ;
               6'b100100: aluOp = `AND ;
               6'b100101: aluOp = `OR ;
               6'b100110: aluOp = `XOR ;
               6'b100111: aluOp = `NOR ;
               6'b101010: aluOp = `SLT ;
               6'b101011: aluOp = `SLTU ;         
            endcase

            PrepareFetch;
         end

         EX_ALU_I: begin
            RegDst = 1'b0;
            MemtoReg = 3'b000;
            aluSelA = 1'b1;
            aluSelB = 3'b010;
            RFwrt = 1'b1;
            
            case(IR[31:26])
               6'b001000,
               6'b001001: begin aluOp = `ADD ; SgnExt = 1'b1 ; end    // addi(u)
               6'b001010: begin aluOp = `SLT ; SgnExt = 1'b1 ; end    // slti
               6'b001011: begin aluOp = `SLTU ; SgnExt = 1'b0 ; end   // sltiu
               6'b001100: begin aluOp = `AND ; SgnExt = 1'b0 ; end    // andi
               6'b001101: begin aluOp = `OR ; SgnExt = 1'b0 ; end     // ori
               6'b001110: begin aluOp = `XOR ; SgnExt = 1'b0 ; end    // xori
            endcase

            PrepareFetch;            
         end

         EX_LW_1: begin
            MARwrt = 1'b1;
            SgnExt = 1'b1;
            setMRE = 1'b1;
            IorD = 1'b1;
            aluSelA = 1'b1;
            aluSelB = 3'b010;
            aluOp = `ADD;
            nxt_state = EX_LW_2;            
         end

         EX_LW_2: begin
            nxt_state = EX_LW_3;
         end

         EX_LW_3: begin
            nxt_state = EX_LW_4;
         end

         EX_LW_4: begin
            clrMRE = 1'b1;
            MDRwrt = 1'b1;
            nxt_state = EX_LW_5;
         end

         EX_LW_5: begin
            MemtoReg = 3'b001;
            RegDst = 1'b0;
            RFwrt = 1'b1;
            PrepareFetch;
         end

         EX_SW_1: begin
            MARwrt = 1'b1;
            SgnExt = 1'b1;
            setMWE = 1'b1;
            IorD = 1'b1;
            aluSelA = 1'b1;
            aluSelB = 3'b010;
            aluOp = `ADD;
            nxt_state = EX_SW_2;
         end

         EX_SW_2: begin
            clrMWE = 1'b1;
            nxt_state = EX_SW_3;
         end

         EX_SW_3: begin
            PrepareFetch;
         end

         EX_BRA_1: begin
            aluSelA = 1'b1;
            aluSelB = 3'b000;
            aluOp = `SUB;

            case(IR[31:26])
               6'b000100 : begin 
                  if(aluZero) nxt_state = EX_BRA_2;
                  else PrepareFetch; 
               end
               6'b000101: begin
                  if(!aluZero) nxt_state = EX_BRA_2;
                  else PrepareFetch; 
               end
            endcase
         end

         EX_BRA_2: begin
            PCwrt = 2'b01;
            MARwrt = 1'b1;
            setMRE = 1'b1;
            SgnExt = 1'b1;
            aluSelA = 1'b0;
            aluSelB = 3'b011;
            aluOp = `ADD;
            IorD = 1'b1;
            nxt_state = FETCH1;

         end

         EX_JR: begin
            PCwrt = 2'b10;
            nxt_state = RESET;
         end

         EX_JALR: begin
            PCwrt = 2'b10;
            aluSelA = 0;
            aluSelB = 3'b100;
            MemtoReg = 3'b000;
            RFwrt = 1;
            aluOp = `ADD;
            RegDst = 1;
            nxt_state = RESET;
         end

         EX_J: begin
            case(IR[31:26])
               6'b000011: begin aluSelA = 0 ; aluSelB = 3'b100 ; MemtoReg = 3'b000 ; RFwrt = 1 ; aluOp = `ADD ; JAL = 1 ; end
               6'b000010: ;
            endcase
            PCwrt = 2'b11;
            nxt_state = RESET;
         end

         EX_LUI: begin
            MemtoReg = 3'b010;
            RegDst = 0;
            RFwrt = 1;
            PrepareFetch;
         end

         EX_MULT_1: begin
            multStart = 1;
            nxt_state = EX_MULT_2;
         end

         EX_MULT_2: begin
            if(multReady)
               nxt_state = RESET;
            else
               nxt_state = EX_MULT_2;
         end

         EX_MFX: begin
            RegDst = 1'b1;
            RFwrt = 1'b1;

            if(IR[2:0] == 3'b000)
               MemtoReg = 3'b011;
            else if(IR[2:0] == 3'b010)
               MemtoReg = 3'b100;

            PrepareFetch;
         end

      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input [2:0] Op,
   input [31:0] A,
   input [31:0] B,

   output [31:0] X,
   output        Z
);

   wire sub = Op != `ADD;

   wire [31:0] bb = sub ? ~B : B;

   wire [32:0] sum = A + bb + sub;

   wire sltu = ! sum[32];

   wire v = sub ? 
        ( A[31] != B[31] && A[31] != sum[31] )
      : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//==============================================================================

module multiplier(
//---------------------Port directions and deceleration
   input clk,  
   input start,
   input [31:0] A, 
   input [31:0] B, 
   output wire [31:0] lower,
   output wire [31:0] higher,
   output ready
    );
//----------------------------------------------------

//--------------------------------- register deceleration
reg [31:0] Multiplicand ;
reg [5:0]  counter;
reg [63:0] adder_output;
//-----------------------------------------------------

//----------------------------------- wire deceleration
wire product_write_enable;
//-------------------------------------------------------

//------------------------------------ combinational logic
assign product_write_enable = adder_output[0];
assign ready = counter[5];
assign lower = adder_output[31:0];
assign higher = adder_output[63:32];
//-------------------------------------------------------

//------------------------------------- sequential Logic
always @ (posedge clk)

   if(start) begin
      counter <= 6'b000000 ;
      adder_output <= {32'h00000000 , B};
      Multiplicand <= A ;
   end

   else if(! ready) begin
      counter <= counter + 1;
      
      if(product_write_enable)
         adder_output <= (adder_output >> 1) + {Multiplicand , 31'b0000000000000000000000000000000};
      else
         adder_output <= adder_output >> 1;
   end   

endmodule