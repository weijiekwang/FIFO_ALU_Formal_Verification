# Clear previous designs and analysis
clear -all

# Analyze and elaborate the design
analyze -sv09 alu_fifo_design.sv
elaborate -top top

# Clock and reset setup
clock clk
reset reset

# Assume initial reset
assume { reset } @ 0

# Basic protocol assertions for FIFO interfaces
assert { top.f_in.wptr >= 0 && top.f_in.wptr < 8 }
assert { top.f_in.rptr >= 0 && top.f_in.rptr < 8 }

# Basic protocol assertions for ALU
assert { top.alu1.count >= 0 && top.alu1.count < 4 }

# Protocol checks
assert { (top.f_in.full == 1) |-> !top.f_in.valid }
assert { (top.f_in.empty == 1) |-> !top.f_in.valid_out }

# Check ALU operation integrity
assert { (top.alu1.operand == 2'b00) |-> (top.alu1.result == (top.alu1.data1 + top.alu1.data2)) }
assert { (top.alu1.operand == 2'b01) |-> (top.alu1.result == (top.alu1.data1 - top.alu1.data2)) }

# Set proof depth
set_max_trace_length 20