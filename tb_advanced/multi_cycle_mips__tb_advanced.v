
`timescale 1ns/10ps

module multi_cycle_mips__tb_advanced;

   reg clk = 1;
   always @(clk)
      clk <= #1.25 ~clk;

   reg reset;
   initial begin
      reset = 1;
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);
      #0.2;
      reset = 0;
   end

   initial
      $readmemh("advanced.hex", mem.mem_data);

   parameter end_mar = 32'h00003078;

   integer i;
   always @(cpu.MAR) begin
      if(cpu.MAR == end_mar) begin
         #1
         for(i=0; i<15; i=i+1)
            $display("%x ", mem.mem_data[50+i]);
         $stop;
      end

   end

   multi_cycle_mips cpu(
      .clk( clk ),
      .reset( reset ),
      .mem_addr( ),
      .mem_read_data( mem.read_data ),
      .mem_write_data(),
      .mem_read( ),
      .mem_write( )
   );

   async_mem mem(
      .clk( clk ),
      .read( cpu.mem_read ),
      .write( cpu.mem_write ),
      .address( cpu.mem_addr ),
      .write_data( cpu.mem_write_data ),
      .read_data());

endmodule

//==============================================================================

module async_mem(
   input clk,
   input read,
   input write,
   input [31:0] address,
   input [31:0] write_data,
   output [31:0] read_data
);

   reg [31:0] mem_data [0:1023];

   assign #7 read_data = read ? mem_data[ address[11:2] ] : 32'bxxxxxxxx;

   always @( posedge clk )
      if ( write )
         mem_data[ address[11:2] ] <= write_data;

endmodule

//==============================================================================
