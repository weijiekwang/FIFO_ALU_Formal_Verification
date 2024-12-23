clear -all

analyze -sv09 alu.sv
elaborate -top ALU

clock clk
reset reset
