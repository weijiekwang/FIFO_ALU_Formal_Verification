clear -all

analyze -sv09 alu_fifo.sv
elaborate -top top

clock clk
reset reset
