        
module ALU_design(out,sign,carr,zero,in);
  output logic [3:0]out; 
  output logic sign,carr,zero; 
  input logic [11:0]in;
  
  logic [3:0]A;
  logic [3:0]B;
  logic [4:0]y;

always@(in)
begin
  A=in[3:0];
  B=in[7:4];
  carr=0;
  sign=0;

  if (y[4:0]==0)zero=1;
  else zero = 0;
  out=y[3:0];
  
  case(in[11:8])
  4'b1101:
     begin
       y=A+B;
       if (y>4'b1111)carr=1;
     end  
  4'b1001:y=A&B;
  4'b0101:y=A[1:0]*B[1:0];
  4'b0001:y=~A;
  4'b1100:y=~(A&B);
  4'b0010:
     begin
        if (B>A)begin
           y=B-A; 
           sign=1;
           end
        else y=A-B;
     end
  4'b0011:y=~(A^B);
  4'b0110:y=~(A|B);
  default y=0;
  endcase
end
// Addition operation assertions
ADD_RESULT_CHECK: assert property(
    @(in) 
    (in[11:8] == 4'b1101) |-> 
    ((out == in[3:0] + in[7:4]) && 
     (carr == ({1'b0, in[3:0]} + {1'b0, in[7:4]} > 5'b01111)) &&
     (zero == (in[3:0] + in[7:4] == 0))));

endmodule: ALU_design