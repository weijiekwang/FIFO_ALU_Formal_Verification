module TWOFIFOWRAPPER #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 8
)(
    input clk,
    input rst_n,
    
    // Common Write Interface
    input wr_en,
    input [DATA_WIDTH-1:0] wr_data,
    
    // Common Read Interface
    input rd_en,
    
    // FIFO1 Outputs
    output wr_ready_1,
    output [DATA_WIDTH-1:0] rd_data_1,
    output rd_valid_1,
    
    // FIFO2 Outputs
    output wr_ready_2,
    output [DATA_WIDTH-1:0] rd_data_2,
    output rd_valid_2
);

    // Instantiate first FIFO
    fifo #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH)
    ) FIFO1 (
        .clk(clk),
        .rst_n(rst_n),
        .wr_en(wr_en),
        .wr_data(wr_data),
        .wr_ready(wr_ready_1),
        .rd_en(rd_en),
        .rd_data(rd_data_1),
        .rd_valid(rd_valid_1)
    );

    // Instantiate second FIFO
    fifo #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH)
    ) FIFO2 (
        .clk(clk),
        .rst_n(rst_n),
        .wr_en(wr_en),
        .wr_data(wr_data),
        .wr_ready(wr_ready_2),
        .rd_en(rd_en),
        .rd_data(rd_data_2),
        .rd_valid(rd_valid_2)
    );

    // Equivalence checking assertions
    
    // Check that ready signals match
    READY_MATCH: assert property(@(posedge clk) disable iff (~rst_n)
        wr_ready_1 == wr_ready_2);
        
    // Check that valid signals match
    VALID_MATCH: assert property(@(posedge clk) disable iff (~rst_n)
        rd_valid_1 == rd_valid_2);
        
    // Check that data matches when reading
    DATA_MATCH: assert property(@(posedge clk) disable iff (~rst_n)
        rd_valid_1 && rd_valid_2 && rd_en |-> rd_data_1 == rd_data_2);

    // Assumptions to prevent invalid operations
    ASSUME_NO_READ_WHEN_EMPTY: assume property(@(posedge clk) disable iff (~rst_n)
        !(rd_valid_1 || rd_valid_2) |-> !rd_en);
        
    ASSUME_NO_WRITE_WHEN_FULL: assume property(@(posedge clk) disable iff (~rst_n)
        !(wr_ready_1 || wr_ready_2) |-> !wr_en);

endmodule