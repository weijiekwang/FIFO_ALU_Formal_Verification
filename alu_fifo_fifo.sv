module top(clk,reset,data,valid,ready,result);
    input clk,reset;
    input [9:0]data;
    input valid;
    output ready;
    output [8:0]result;
    
    wire [9:0]data_out_fifo;
    wire [8:0]data_out_alu;
    wire ready_out_alu;
    wire full,empty,valid_out;
    wire full_out,empty_out;
    
    fifo f_in(clk,reset,data,data_out_fifo,valid,valid_out,ready_out_alu,full,empty);
    alu alu1(clk,reset,valid_out,data_out_fifo[3:0],data_out_fifo[7:4],data_out_fifo[9:8],data_out_alu,ready_out_alu);
    fifo #(.memory_width(8)) f_out(clk,reset,data_out_alu,result,ready_out_alu,ready,ready_out_alu,full_out,empty_out);
    
endmodule
  
module fifo(clk,reset,data_in,data_out,valid,valid_out,ready,full,empty);
    parameter memory_width = 9;
    parameter depth = 8;
    

    input clk,reset;
    input [memory_width:0]data_in;
    output reg [memory_width:0]data_out;
    input ready;
    input valid;
    output reg valid_out;
    output reg full,empty;
    
    reg [memory_width:0] mem [8];
    reg [2:0]wptr;
    reg [2:0]rptr;
    reg [1:0]state;
    reg reset_done;
    reg update_done;
    
    // state 
    parameter send = 2'b00;
    parameter wait_ready = 2'b01;
    parameter end_tx = 2'b10;
  
    always@(posedge clk or posedge reset) begin
        if (reset) begin
            wptr[0] <= 0;
            wptr[1] <= 0;
            wptr[2] <= 0;
            rptr <= 0;
            valid_out <= 0;
            full <= 0;
            empty <= 1;
            state <= 0;
            reset_done <= 0;
            update_done <=0;
            for (int i = 0; i < 8; i++) begin
               mem[i] <= 0;
            end
        end
        else if (!reset_done && !update_done) begin
                if (valid) begin
                      reset_done <= 1;
                      mem[wptr] <= data_in;
                      empty <= 0;
                      if (wptr == (depth -1)) begin 
                          wptr <=0;
                          end else begin
                          wptr <= wptr+1;                     
                      end
                end
        end 
        else if(reset_done) begin
             if(!update_done) begin
                if(valid && !full) begin
                      mem[wptr] <= data_in;
                      wptr <= wptr + 1;
                end
                else if(!empty) begin
                     case (state)
                           send: begin
                                data_out <= mem[rptr];
                                valid_out <= 1;
                                if (rptr == (depth -1)) begin 
                                rptr <=0;
                                end else begin
                                rptr <= rptr+1;                     
                                end
                              if(ready)
                              state <= end_tx;
                              else
                              state <= wait_ready;
                           end
                           wait_ready: begin
                              if(ready)
                              state <= end_tx;
                              else
                              state <= wait_ready;
                           end
                           end_tx: begin
                              valid_out <= 0;
                              state <= send;
                           end
                     endcase
                end
                update_done <= 1;
             end else if(update_done) begin
                 if(wptr == (rptr -1)) begin
                    full <= 1;
                    empty <= 0;
                 end
                 else if (rptr == wptr) begin
                    empty <= 1;
	            full  <= 0;
	         end
             update_done <= 0;              
             end       
        end
    end

// reset: fifo ->reset
fifo_reset1: assert property (@(posedge reset) (empty && !full && (wptr == 0) && (rptr == 0) && (state == 0) && valid_out == 0));

// reset: fifo -> !valid  && !ready 
fifo_reset2: assert property (@(posedge reset) (!valid && !ready));

// verify the full
FIFO_full: assert property (@(posedge clk) $past(valid && wptr == (rptr - 1)) |-> full && !empty);

// verify the empty
FIFO_empty: assert property (@(posedge clk) $past(valid && (wptr == rptr) && reset_done) |-> !full && empty);

//cover wptr add
FIFO_wptr: cover property (@(posedge clk) 
    (wptr != 7) |-> (wptr == $past(wptr) + 1));

//cover rptr add
FIFO_rptr: cover property (@(posedge clk) 
    (rptr != 7) |-> (rptr == $past(rptr) + 1));

//fifo full -> no change
FIFI_write_full: assert property (@(posedge clk) full && valid |-> (wptr == $past(wptr)));

// fifo empty -> no change
FIFO_read_emtpy: assert property (@(posedge clk) empty && ready |-> (rptr == $past(rptr)));





       
endmodule
        
module alu(clk,reset,valid,data1,data2,operand,result,ready);

    parameter cycles = 3;
    
    input clk,reset;
    input valid;// only valid == 0, the alu could work
    input [3:0]data1,data2;
    input [1:0]operand;
    output reg [8:0]result;
    output reg ready;// could process the new data
    
    //precess the multi and divide
    reg [4:0]count = 0; //connect FSM, count cycles -> state(compute/wait_state)
    reg [1:0]operand_latch;
    reg [3:0]data1_latch,data2_latch; // lock data ,keep value
    reg [1:0]state; //2 bits
    
    parameter compute = 1'b0;
    parameter wait_state = 1'b1;
  
    always@(posedge reset)
      begin
        ready <= 1;
        result <= 0;
        count <= 0;
        state <= 0;
      end
    
    always@(posedge clk)
      begin
        case(state)        
          compute: begin
            case(operand)
              0: begin 
                result <= data1+data2;
                state <= compute;
              end
              1: begin
                result <= data1-data2;
                state <= compute;
              end
              2: begin
                state <= wait_state;
                operand_latch <= operand;
                data1_latch <= data1;
                data2_latch <= data2;
              end
              3: begin
                state <= wait_state;
                operand_latch <= operand;
                data1_latch <= data1;
                data2_latch <= data2;
              end
            endcase
          end
          wait_state: begin
            case(operand_latch)
              2: begin
                if(count == cycles-1) begin
                  result <= data1_latch*data2_latch;
                  ready <= 1;
                  count <= 0;
                  state <= compute;
                end
                else begin
                  count <= count + 1;
                  ready <= 0;
                end
              end
              3: begin
                if(count == cycles-1) begin
                  result <= data1_latch/data2_latch;
                  ready <= 1;
                  count <= 0;
                  state <= compute;
                end
                else begin
                  count <= count + 1;
                  ready <= 0;
                end
              end
            endcase
          end
        endcase
      end
         
endmodule
