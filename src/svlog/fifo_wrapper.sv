module fifo_wrapper( clk, rst, in_read_ctrl, in_write_ctrl, in_write_data, 
             out_read_data, out_is_full, out_is_empty
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

   logic [ENTRIES_LOG2-1:0]  write_ptr;
   logic [ENTRIES_LOG2-1:0]  read_ptr;
   logic [ENTRIES-1:0] [7:0] fifo_data;
   logic [7:0]               head;
   logic [ENTRIES_LOG2:0]    number_of_current_entries; 

   logic                     out_is_full_tmp;   
   logic                     out_is_empty_tmp;
   logic                     last_out_is_empty;
   logic                     last_out_is_full; 
   
   logic                     fifo_is_correct; 

   fifo
      #(.ENTRIES(ENTRIES))
   fifo_inst
     (.clk(clk),
      .rst(rst),
      .in_read_ctrl(in_read_ctrl),
      .in_write_ctrl(in_write_ctrl),
      .in_write_data(in_write_data),
      .out_read_data(out_read_data),
      .out_is_full(out_is_full_tmp),
      .out_is_empty(out_is_empty_tmp));


always_comb  begin
   if (fifo_is_correct) begin
      out_is_full = out_is_full_tmp;
      out_is_empty = out_is_empty_tmp;
   end
   else begin 
      out_is_full = last_out_is_full;
      out_is_empty = last_out_is_empty;
   end
end

always_ff @(posedge clk) begin
   if (rst) begin
      last_out_is_full <= 0;
      last_out_is_empty <= 1;
   end
   else begin
      fifo_is_correct <= in_read_ctrl | in_write_ctrl;
      last_out_is_full <= out_is_full;
      last_out_is_empty <= out_is_empty;
   end
end

fifo_assume_entry_empty:
   assume property (@(posedge clk) out_is_empty |-> ~in_read_ctrl);
fifo_assume_entry_full:
   assume property (@(posedge clk) out_is_full |-> ~in_write_ctrl);

wire [2:0] fifo_fire;

ovl_fifo_index #(
   .depth(ENTRIES)
)
fifo_checker(
   .clock(clk),
   .reset(!rst),
   .enable(1'b1),
   .push(in_write_ctrl),
   .pop(in_read_ctrl),
   .fire(fifo_fire)
);

endmodule
   
