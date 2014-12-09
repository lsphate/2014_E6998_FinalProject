module fifo(clk, rst, in_read_ctrl, in_write_ctrl, in_write_data,
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

always_ff @(posedge clk) begin
   if (rst) begin
      write_ptr <= 0;
   end
   else if (in_write_ctrl) begin
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
   end
   else if (in_read_ctrl) begin
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
   else if (~in_read_ctrl & ~in_write_ctrl) begin
      out_is_empty <= 0;
      out_is_full <= 0;
   end
end
/*
fifo_assume_entry_empty:
   assume property (@(posedge clk) out_is_empty |-> ~in_read_ctrl);
fifo_assume_entry_full:
   assume property (@(posedge clk) out_is_full |-> ~in_write_ctrl);

fifo_cover_entrynum_7:
   cover property (@(posedge clk) number_of_current_entries == 3'b111);
fifo_cover_entrynum_6:
   cover property (@(posedge clk) number_of_current_entries == 3'b110);
fifo_cover_entrynum_5:
   cover property (@(posedge clk) number_of_current_entries == 3'b101);
fifo_cover_entrynum_4:
   cover property (@(posedge clk) number_of_current_entries == 3'b100);
fifo_cover_entrynum_3:
   cover property (@(posedge clk) number_of_current_entries == 3'b011);
fifo_cover_entrynum_2:
   cover property (@(posedge clk) number_of_current_entries == 3'b010);
fifo_cover_entrynum_1:
   cover property (@(posedge clk) number_of_current_entries == 3'b001);
fifo_cover_entrynum_0:
   cover property (@(posedge clk) number_of_current_entries == 3'b000);
*//*
generate
for (genvar i = 0; i < (1 << (ENTRIES_LOG2 + 1)); i++) begin
   cover property (@(posedge clk) number_of_current_entries == i);
end
endgenerate
*//*
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
*/
endmodule
