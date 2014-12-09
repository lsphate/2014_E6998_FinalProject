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


Thus we turn to check the wave form of on fire (the highlight one). According to the diagram, we figure out that the bug could happen during reset. As **fifo_wrapper.sv** is a "patch" of the former **fifo.sv**, it implements an mechanism to check if the result of **fifo.sv** is correct, i.e. the *fifo_is_correct*, *out_is_full_tmp*, *out_is_empty_tmp*, *last_out_is_empty*, and *last_out_is_full*.
![Wave Form befor debug](http://i.imgur.com/zQuJtZu.jpg)

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