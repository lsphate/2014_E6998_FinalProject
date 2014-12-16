#Formal Verification Coverage Closure Project

*Sun-Yi Lin (sl3833)*  
*Jie-Gang Kuang (jk3735)*

#Phase II

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

![Covered properties](http://i.imgur.com/K39OekI.png)

###C.
Seeing the wave form of entrynum 5, we can notice that the number_of_current_entries has been decreased by 1 even if it was 0. This cause the variable overflowed, becoming 0x111.

![Wave form of entrynum is 5](http://i.imgur.com/Kv5rQlD.png)

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

![Wave form of entrynum is 5 (cont.)](http://i.imgur.com/cM7aZ3y.png)

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

![Properties after modification.](http://i.imgur.com/SsalMQA.png)

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

![OVL checker properties](http://i.imgur.com/qq0ppLv.png)

###B.
A possible bug could be as follows:

```
-   logic [ENTRIES_LOG2:0]    number_of_current_entries;
+   logic [ENTRIES_LOG2-1:0]    number_of_current_entries;
```

If the codes were modified as the above, the OVL fifo checker can pass. However, the coverage check will fail. Since there are only 3 bits to count the number of current entries, it will never become 4.


#Phase III

To begin with this nwe phase, We put the 2 new file **fifo_wrapper.sv**, **fifo_with_error_checker.sv** in to our work directory in Phase II and modify the **Makefile** to make and run them.

##Task 1
First, we copy these two assumptions into the **fifo_wrapper.sv**:

```
fifo_assume_entry_empty:
   assume property (@(posedge clk) out_is_empty |-> ~in_read_ctrl);
fifo_assume_entry_full:
   assume property (@(posedge clk) out_is_full |-> ~in_write_ctrl);
```
And add this piece of code to check if could the fifo become overflowed or not:

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

After doing the OVL checker, we notice that there are 2 **fires**, indicates this fifo could both become overflowed or underflowed.

![Properties before debug](http://i.imgur.com/APRldCn.jpg)

Thus we turn to check the waveform of on fire (the highlight one). According to the diagram, we figure out that the bug could happen during reset. As **fifo_wrapper.sv** is a "patch" of the former **fifo.sv**, it implements an mechanism to check if the result of **fifo.sv** is correct, i.e. the *fifo_is_correct*, *out_is_full_tmp*, *out_is_empty_tmp*, *last_out_is_empty*, and *last_out_is_full*.

![Waveform befor debug](http://i.imgur.com/zQuJtZu.jpg)

When something is wrong happened in **fifo.sv** (*in_read_ctrl*, *in_write_ctrl*), the *fifo_is_correct* will become 0, and the **fifo_wrapper.sv** will turn to output the previous result (*last_out_is_empty*, *last_out_is_full*) instead of current ones (*out_is_full_tmp*, *out_is_empty_tmp*).

So here comes the problem, what if the fifo goes wrong in the vary beginning? There would be nothing in  *last_out_is_empty* and *last_out_is_full*! To solve problem, we modify a little bunch of code:


```
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
```

And the result become correct this time.

![Properties after debug](http://i.imgur.com/nZ5ebCF.jpg)

##Task 2

###A., B. & C.
When assumptions are implemented, it means that we make the model checker ignore some kinds of inputs, e.g. xx11x(the fifo is full and empty in the same time), 1x1xx(overflowed), x1x1x(underflowed). For such cases, the checker will claim they are "unreachable." For those cases that need to be determined by "excluding" the assumptions, the checker will claim they are "inconclusive" since they are not available because the transitions are blocked by our assumptions. 

![Properties(with assumptions)](http://i.imgur.com/C9o9q0i.png)

If we remove these assumptions, that means we let the checker to inspect every state without any constraint, i.e. the fifo can both become overflowed or underflowed now. In this case, the checker will only claim those states that are both full and empty in the sametime. And for the rest, we need to check the error bit and, if necessary, to see the waveform to figure out where the error occured. However, the functionality of the error bit should be correct. In the source code, the error bit seems to work only when the fifo underflows.

![Properties(w/o assumptions)](http://i.imgur.com/hQwXTWe.png)

With the above observation, we think that it should be necessary and reasonable to add the assumptions for the checker. From the results with assumptions, we can claim that the fifo module is correct if the upstream/downstream module correctly control *in_write_ctrl*/*in_read_ctrl* based on *out_is_full*/*out_is_empty*.

###D.
In verifying the correctness of the fifo, we think the new metric could be not quite helpfull combining with the coverage test. With the assumptions, the coverage test can easily identify the wrong path without the error bit; without the assumptions, almost all possible paths are covered and the error bit becomes indecisive because we have to walk through all the paths to see how the error state is reached.