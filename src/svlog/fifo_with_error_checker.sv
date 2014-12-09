module fifo( clk, rst, in_read_ctrl, in_write_ctrl, in_write_data, 
             out_read_data, out_is_full, out_is_empty, error
             );

   
parameter
  ENTRIES = 4; 
  
localparam [31:0]  
  ENTRIES_LOG2 = $clog2(ENTRIES);
  
   input  logic       clk; 
   input  logic       rst;
   input  logic       in_read_ctrl;
   input  logic       in_write_ctrl;
   input  logic [7:0] in_write_data;
   output logic [7:0] out_read_data;
   output logic       out_is_full;
   output logic       out_is_empty;
   output logic       error;

   logic [ENTRIES_LOG2-1:0]  write_ptr;
   logic [ENTRIES_LOG2-1:0]  read_ptr;
   logic [ENTRIES-1:0] [7:0] fifo_data;
   logic [7:0]               head;
   logic [ENTRIES_LOG2:0]    number_of_current_entries; 

   logic [31:0]              count_ingoing;
   logic [31:0]              count_outgoing;

   
always_ff @(posedge clk) begin
   if (rst) begin
      write_ptr <= 0;
      count_ingoing <= 0;
   end
   else if (in_write_ctrl) begin
      count_ingoing <= count_ingoing + 1'b1; 
      write_ptr <= write_ptr + 1'b1;
      fifo_data[write_ptr] <= in_write_data;
   end
end

always_comb begin
   head = fifo_data[read_ptr];
end
   
always_ff @(posedge clk) begin
   if (rst) begin
      read_ptr <= 0;
      count_outgoing <= 0;
   end
   else if (in_read_ctrl) begin
      count_outgoing <= count_outgoing + 1'b1;
      read_ptr <= read_ptr + 1'b1;
      out_read_data <= head;
   end
end

always_ff @(posedge clk) begin
   if (rst) begin
      number_of_current_entries <= 0;
      out_is_empty <= 1;
      out_is_full <= 0;
   end
   else if (in_read_ctrl & ~in_write_ctrl ) begin
      number_of_current_entries <= number_of_current_entries - 1'b1;
      out_is_full <= 0;
      out_is_empty <= (number_of_current_entries == 1'b1);       
   end
   else if (~in_read_ctrl & in_write_ctrl) begin
      number_of_current_entries <= number_of_current_entries + 1'b1;
      out_is_empty <= 0;
      out_is_full <= (number_of_current_entries == (ENTRIES-1'b1)); 
   end
end

always_comb begin
   error = (count_ingoing < count_outgoing);
end

my_assume_1: assume property (@(posedge clk) 
                              out_is_full |-> !in_write_ctrl);

my_assume_2: assume property (@(posedge clk) 
                              out_is_empty |-> !in_read_ctrl);

/** Coverage **/
covmet_inout_00000_covered:
   cover property (@(posedge clk)
   !in_write_ctrl && !in_read_ctrl && !out_is_full && !out_is_empty && !error);

covmet_inout_00001:
   cover property (@(posedge clk)
   !in_write_ctrl && !in_read_ctrl && !out_is_full && !out_is_empty && error);

covmet_inout_00010_covered:
   cover property (@(posedge clk)
   !in_write_ctrl && !in_read_ctrl && !out_is_full && out_is_empty && !error);

covmet_inout_00011:
   cover property (@(posedge clk)
   !in_write_ctrl && !in_read_ctrl && !out_is_full && out_is_empty && error);

covmet_inout_00100_covered:
   cover property (@(posedge clk)
   !in_write_ctrl && !in_read_ctrl && out_is_full && !out_is_empty && !error);

covmet_inout_00101:
   cover property (@(posedge clk)
   !in_write_ctrl && !in_read_ctrl && out_is_full && !out_is_empty && error);

covmet_inout_00110:
   cover property (@(posedge clk)
   !in_write_ctrl && !in_read_ctrl && out_is_full && out_is_empty && !error);

covmet_inout_00111:
   cover property (@(posedge clk)
   !in_write_ctrl && !in_read_ctrl && out_is_full && out_is_empty && error);

covmet_inout_01000_covered:
   cover property (@(posedge clk)
   !in_write_ctrl && in_read_ctrl && !out_is_full && !out_is_empty && !error);

covmet_inout_01001:
   cover property (@(posedge clk)
   !in_write_ctrl && in_read_ctrl && !out_is_full && !out_is_empty && error);

covmet_inout_01010:
   cover property (@(posedge clk)
   !in_write_ctrl && in_read_ctrl && !out_is_full && out_is_empty && !error);

covmet_inout_01011:
   cover property (@(posedge clk)
   !in_write_ctrl && in_read_ctrl && !out_is_full && out_is_empty && error);

covmet_inout_01100_covered:
   cover property (@(posedge clk)
   !in_write_ctrl && in_read_ctrl && out_is_full && !out_is_empty && !error);

covmet_inout_01101:
   cover property (@(posedge clk)
   !in_write_ctrl && in_read_ctrl && out_is_full && !out_is_empty && error);

covmet_inout_01110:
   cover property (@(posedge clk)
   !in_write_ctrl && in_read_ctrl && out_is_full && out_is_empty && !error);

covmet_inout_01111:
   cover property (@(posedge clk)
   !in_write_ctrl && in_read_ctrl && out_is_full && out_is_empty && error);

covmet_inout_10000_covered:
   cover property (@(posedge clk)
   in_write_ctrl && !in_read_ctrl && !out_is_full && !out_is_empty && !error);

covmet_inout_10001:
   cover property (@(posedge clk)
   in_write_ctrl && !in_read_ctrl && !out_is_full && !out_is_empty && error);

covmet_inout_10010_covered:
   cover property (@(posedge clk)
   in_write_ctrl && !in_read_ctrl && !out_is_full && out_is_empty && !error);

covmet_inout_10011:
   cover property (@(posedge clk)
   in_write_ctrl && !in_read_ctrl && !out_is_full && out_is_empty && error);

covmet_inout_10100:
   cover property (@(posedge clk)
   in_write_ctrl && !in_read_ctrl && out_is_full && !out_is_empty && !error);

covmet_inout_10101:
   cover property (@(posedge clk)
   in_write_ctrl && !in_read_ctrl && out_is_full && !out_is_empty && error);

covmet_inout_10110:
   cover property (@(posedge clk)
   in_write_ctrl && !in_read_ctrl && out_is_full && out_is_empty && !error);

covmet_inout_10111:
   cover property (@(posedge clk)
   in_write_ctrl && !in_read_ctrl && out_is_full && out_is_empty && error);

covmet_inout_11000_covered:
   cover property (@(posedge clk)
   in_write_ctrl && in_read_ctrl && !out_is_full && !out_is_empty && !error);

covmet_inout_11001:
   cover property (@(posedge clk)
   in_write_ctrl && in_read_ctrl && !out_is_full && !out_is_empty && error);

covmet_inout_11010:
   cover property (@(posedge clk)
   in_write_ctrl && in_read_ctrl && !out_is_full && out_is_empty && !error);

covmet_inout_11011:
   cover property (@(posedge clk)
   in_write_ctrl && in_read_ctrl && !out_is_full && out_is_empty && error);

covmet_inout_11100:
   cover property (@(posedge clk)
   in_write_ctrl && in_read_ctrl && out_is_full && !out_is_empty && !error);

covmet_inout_11101:
   cover property (@(posedge clk)
   in_write_ctrl && in_read_ctrl && out_is_full && !out_is_empty && error);

covmet_inout_11110:
   cover property (@(posedge clk)
   in_write_ctrl && in_read_ctrl && out_is_full && out_is_empty && !error);

covmet_inout_11111:
   cover property (@(posedge clk)
   in_write_ctrl && in_read_ctrl && out_is_full && out_is_empty && error);

endmodule
