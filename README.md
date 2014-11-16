#Formal Verification Phase II
To do these tasks, we copied and modified the tutorials in the phase I. We merged the **fifo.sv** into the tutorial and modified the **Makefile** to make it work.
##Task 1
###A.
We modified the **fifo.sv** and put it in *src/svlog/*, and the added cover properties are listed below:
```
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
```
###B.
All the properties are covered.
###C.
Seeing the wave form of entrynum 5, we can notice that the number_of_current_entries has been decreased by 1 even if it was 0. This cause the variable overflowed, becoming 0x111.

![Picture1](http://i.imgur.com/Kv5rQlD.png?2)

This is that piece of code in the **fifo.sv**:
```
else if (in_read_ctrl & ~in_write_ctrl ) begin
	number_of_current_entries <= number_of_current_entries - 1'b1;
	out_is_full <= 0;
	out_is_empty <= (number_of_current_entries == 1'b1);
end
```
###D.
To add assumptions to constrain the conditions, we added the following codes into the **fifo.sv**:
```
fifo_assume_entry_empty:
	assume property (@(posedge clk) out_is_empty |-> ##[0:1] ~in_read_ctrl);
fifo_assume_entry_full:
	assume property (@(posedge clk) out_is_full |-> ##[0:1] ~in_write_ctrl);
```
###E.
We run the test again with the additional assumptions.
###F.
Analyze the wave form and we will notice that the variable "out_is_empty" will aribitarily become 0 even when there is no writing.

![Picture 2](http://i.imgur.com/cM7aZ3y.png?2)

###G.
The bug is because of these 2 line:
```
out_is_empty <= 0;
out_is_full <= 0;
```
###H.
We try to fix the bug by adding these 2 lines:
```
out_is_empty <= out_is_empty;
out_is_full <= out_is_full;
```
###I.
After our modification, the entrynum from 4 to 7 is not covered anymore:

![Picture 3](http://i.imgur.com/SsalMQA.png?1)
