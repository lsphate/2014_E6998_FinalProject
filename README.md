#Formal Verification Phase II
*Sun-Yi Lin (sl3833)*  
*Jie-Gang Kuang (jk3735)*

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
All the properties are covered as follows:

![Picture1](http://i.imgur.com/K39OekI.png)

###C.
Seeing the wave form of entrynum 5, we can notice that the number_of_current_entries has been decreased by 1 even if it was 0. This cause the variable overflowed, becoming 0x111.

![Picture2](http://i.imgur.com/Kv5rQlD.png)

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
After running the test again, the coverage is still the same. Analyzed the wave form and we noticed that the variable "out_is_empty" was aribitarily set 0 even when there is no writing.

![Picture 3](http://i.imgur.com/cM7aZ3y.png)

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

![Picture 4](http://i.imgur.com/SsalMQA.png)

##Task 2
In the Task 1, the running time with 4-entry queue is:

	# ---------------------------------------
	# Property Summary                  Count
	# ---------------------------------------
	# Assumed                               2
	# Covered                               5
	# Inconclusive                          0
	# Uncoverable                           3
	# ---------------------------------------
	# Total                                10
	# ---------------------------------------
	#
	#
	# --------- Process Statistics ----------
	# Elapsed Time (s):                     2
	# -------------- remote:0 ---------------
	# Total CPU Time (s):                   2
	# Memory Used (MB):                  1089
	# ---------------------------------------

To accommodate the different sizes of the queue, we modified the codes of cover property as follows:
```
generate
for (genvar i = 0; i < (1 << (ENTRIES_LOG2 + 1)); i++) begin
   cover property (@(posedge clk) number_of_current_entries == i);
end
endgenerate
```
With the above modification and setting the number of entries to 64, we can the statistics of running time:
	# ---------------------------------------
	# Property Summary                  Count
	# ---------------------------------------
	# Assumed                               2
	# Covered                              65
	# Inconclusive                          0
	# Uncoverable                          63
	# ---------------------------------------
	# Total                               130
	# ---------------------------------------
	#
	#
	# --------- Process Statistics ----------
	# Elapsed Time (s):                   323
	# -------------- remote:0 ---------------
	# Total CPU Time (s):                 323
	# Memory Used (MB):                  1089
	# ---------------------------------------
The formal runs take longer because they need to make sure whether the cover properties are covered or not. To test that, all the possible path should be tested. If it is proportional to the number of possible values which increase exponentially, then the running time will increase exponentially.
Setting number of entries to 64 is kind of acceptable limit, since it took around 10 minutes with 128 as the number of entries:
	# ---------------------------------------
	# Property Summary                  Count
	# ---------------------------------------
	# Assumed                               2
	# Covered                             129
	# Inconclusive                          0
	# Uncoverable                         127
	# ---------------------------------------
	# Total                               258
	# ---------------------------------------
	#
	#
	# --------- Process Statistics ----------
	# Elapsed Time (s):                   552
	# -------------- remote:0 ---------------
	# Total CPU Time (s):                 552
	# Memory Used (MB):                  2113
	# ---------------------------------------
With the result, we can also observe that the running time is also nearly doubled compared to number of entries of 64, which comforms our explanation.
##Task 3
###A.
We added the following codes to add a OVL FIFO checker in the **fifo.sv**:
```
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
```
With the added the OVL checker, the formal run shows the properties are proved:

![Picture5](http://i.imgur.com/qq0ppLv.png)