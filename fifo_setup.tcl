# Clear previous designs and analysis
clear -all

# Analyze and elaborate the design
analyze -sv09 alu_fifo_design.sv
elaborate -top top

# Clock and reset setup
clock clk
reset reset


# Basic protocol assertions for FIFO interfaces
assert -name fifo_wptr_bound {f_in.wptr >= 0 && f_in.wptr < 8}
assert -name fifo_rptr_bound {f_in.rptr >= 0 && f_in.rptr < 8}

# Basic protocol assertions for ALU
assert -name alu_count_bound {alu1.count >= 0 && alu1.count < 4}

# Protocol checks
assert -name full_valid_check {(f_in.full == 1) |-> !f_in.valid}
assert -name empty_valid_check {(f_in.empty == 1) |-> !f_in.valid_out}

# Check ALU operation integrity
assert -name alu_add_check {(alu1.operand == 2'b00) |-> (alu1.result == (alu1.d$
assert -name alu_sub_check {(alu1.operand == 2'b01) |-> (alu1.result == (alu1.d$

# Set proof depth
set_max_trace_length 20
