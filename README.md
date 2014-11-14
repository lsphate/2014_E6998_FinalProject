#Formal Verification Phase II
##Task 1
###A.
We modify the **fifo.sv** and put it in *src/svlog/*, the cover proverties is list below:

	fifo_cover_entrynum_7:
		cover property (@(posedge clk) ~rst & number_of_current_entries == 3'd7);
	fifo_cover_entrynum_6:
		cover property (@(posedge clk) ~rst & number_of_current_entries == 3'd6);
	fifo_cover_entrynum_5:
		cover property (@(posedge clk) ~rst & number_of_current_entries == 3'd5);
	fifo_cover_entrynum_4:
		cover property (@(posedge clk) ~rst & number_of_current_entries == 3'd4);
	fifo_cover_entrynum_3:
		cover property (@(posedge clk) ~rst & number_of_current_entries == 3'd3);
	fifo_cover_entrynum_2:
		cover property (@(posedge clk) ~rst & number_of_current_entries == 3'd2);
	fifo_cover_entrynum_1:
		cover property (@(posedge clk) ~rst & number_of_current_entries == 3'd1);
	fifo_cover_entrynum_0:
		cover property (@(posedge clk) ~rst & number_of_current_entries == 3'd0);		
###B.
All the properties are covered.

###C.
Seeing the wave form of entrynum 5, we can notice that the number_of_current_entries has been decreased by 1 even it is already 0. This cause the veriable overflowed.

![Picture](http://i.imgur.com/Kv5rQlD.png?2)

This is that piece of code in fifo.sv:

	else if (in_read_ctrl & ~in_write_ctrl ) begin
      number_of_current_entries <= number_of_current_entries - 1'b1;
      out_is_full <= 0;
      out_is_empty <= (number_of_current_entries == 1'b1);
    end

###D.