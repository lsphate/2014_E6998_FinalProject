#Formal Verification Phase III
*Sun-Yi Lin (sl3833)*  
*Jie-Gang Kuang (jk3735)*

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