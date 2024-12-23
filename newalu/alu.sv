module ALU #(parameter DATA_WIDTH = 8)
       (input [DATA_WIDTH-1:0] operandA,
        input [DATA_WIDTH-1:0] operandB,
        input [2:0] opcode,
        output [DATA_WIDTH-1:0] result,
        output zero,
        output carry);

    // Internal wire declarations
    reg  [DATA_WIDTH-1:0] result_t; 
    wire [DATA_WIDTH:0] sum;    // Stores the result_t of addition
    wire [DATA_WIDTH-1:0] difference;    // Stores the result_t of subtraction
    wire [DATA_WIDTH-1:0] bitwiseAnd;    // Stores the result_t of bitwise AND
    wire [DATA_WIDTH-1:0] bitwiseOr;     // Stores the result_t of bitwise OR
    wire [DATA_WIDTH-1:0] bitwiseXor;    // Stores the result_t of bitwise XOR
    wire [DATA_WIDTH-1:0] shiftLeft;     // Stores the result_t of left shift
    wire [DATA_WIDTH-1:0] shiftRight;    // Stores the result_t of right shift

    // Adder
    assign sum = operandA + operandB;

    // Subtractor
    assign difference = operandA - operandB;

    // Bitwise AND
    assign bitwiseAnd = operandA & operandB;

    // Bitwise OR
    assign bitwiseOr = operandA | operandB;

    // Bitwise XOR
    assign bitwiseXor = operandA ^ operandB;

    // Left Shift
    assign shiftLeft = operandA << operandB;

    // Right Shift
    assign shiftRight = operandA >> operandB;


    // result_t selection based on opcode
    always @(*)
    begin
        case (opcode)
            3'b000: result_t = sum;         // Addition
            3'b001: result_t = difference;  // Subtraction
            3'b010: result_t = bitwiseAnd;  // Bitwise AND
            3'b011: result_t = bitwiseOr;   // Bitwise OR
            3'b100: result_t = bitwiseXor;  // Bitwise XOR
            3'b101: result_t = shiftLeft;   // Left Shift
            3'b110: result_t = shiftRight;  // Right Shift
            default: result_t = 0;          // Default case (no operation)
        endcase
    end

    // Zero detection
    assign zero = (result_t == 0);

    // Carry detection
    assign carry = (sum[DATA_WIDTH] != 0);

    assign result = result_t;

// Addition check
ADD_RESULT_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (opcode == 3'b000) |-> (result == operandA + operandB));

// Subtraction check
SUB_RESULT_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (opcode == 3'b001) |-> (result == operandA - operandB));

// AND operation check
AND_RESULT_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (opcode == 3'b010) |-> (result == (operandA & operandB)));

// OR operation check
OR_RESULT_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (opcode == 3'b011) |-> (result == (operandA | operandB)));

// XOR operation check
XOR_RESULT_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (opcode == 3'b100) |-> (result == (operandA ^ operandB)));

// Left shift check
SHIFT_LEFT_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (opcode == 3'b101) |-> (result == (operandA << operandB)));

// Right shift check
SHIFT_RIGHT_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (opcode == 3'b110) |-> (result == (operandA >> operandB)));

// Zero flag check
ZERO_FLAG_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    zero |-> (result == 0));

// Carry flag check for addition
CARRY_FLAG_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (opcode == 3'b000) |-> (carry == ((operandA + operandB) > ((1 << DATA_WIDTH) - 1))));

// Default case check
DEFAULT_CASE_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (opcode == 3'b111) |-> (result == 0));

// Verify zero flag is set correctly when result is 0
ZERO_FLAG_SET_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (result == 0) |-> zero);

// Verify zero flag is not set when result is non-zero
ZERO_FLAG_CLEAR_CHECK: assert property(
    @(posedge clk) disable iff (~rst_n)
    (result != 0) |-> !zero);

endmodule