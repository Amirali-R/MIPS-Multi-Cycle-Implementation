# MIPS-Multi-Cycle-Implementation

A multi cycle implementation of 32-bit processor MIPS using Verilog

## Supported Instructions
### R-Format Instructuions
add, sub, addu, subu, and, or, xor, nor, slt, sltu, jr, jalr, multu, mfhi, mflo
### I-Format Instructuions
 addi, addiu, slti, sltiu, andi, ori, xori, lui, beq, bne, lw, sw
### J-Format Instructuions
j, jal

## Some Notes
1. The exceptions related to instructions sub, addi, add are overlooked.
2. Three series of test bench files are also included for verification. Please refer to Persian PDF file in each test bench folder for further information.

## Time Properties
Time property of each building block used in the circuit is as follows:
### Memory
1. Address to Read-Data propagation delay: 7 ns
2. Write to Read/Write access time: 2 ns
3. Write-Data setup time: 0.1 ns
4. Write is controlled by positive edge of clock
### Register File
1. Read-Register to Read-Data propagation delay: 2 ns
2. Write-Register & Write-Data setup time: 0.1 ns
### Registers
1. Clock to Q delay: 0.1 ns
2. Input setup time: 0.1 ns
### ALU
Inputs to Outputs propagation delay: 2 ns
### Multiplexers
Inputs to Output propagation delay: 0.1 ns
### Clock
Clock Period: 2.5 ns
