///////////////////////////////////////////////////////////////////////////////
//
//               Copyright 2006-2012 Mentor Graphics Corporation
//                          All Rights Reserved.
//  
//             THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY
//           INFORMATION WHICH IS THE PROPERTY OF MENTOR GRAPHICS 
//          CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE
//                                 TERMS.
//
///////////////////////////////////////////////////////////////////////////////

module fifo_checker_sva(clk, rst, number_of_current_entries);
input       clk, rst;
input [2:0] number_of_current_entries;

default clocking c0 @(posedge clk); endclocking

// Single-grant check
// arb_single_grant: assert property (disable iff(rst)  ($onehot(gnt) || gnt == 'b0));

// Known-grant checks
// arb_known_grant_4: assert property (disable iff(rst) gnt[4] |-> $past(req[4],1));
// arb_known_grant_3: assert property (disable iff(rst) gnt[3] |-> $past(req[3],1));
// arb_known_grant_2: assert property (disable iff(rst) gnt[2] |-> $past(req[2],1));
// arb_known_grant_1: assert property (disable iff(rst) gnt[1] |-> $past(req[1],1));
// arb_known_grant_0: assert property (disable iff(rst) gnt[0] |-> $past(req[0],1));

// Coverage: number of current entry
fifo_cover_entrynum_6: cover property (~rst & number_of_current_entries = 3'd6);
fifo_cover_entrynum_5: cover property (~rst & number_of_current_entries = 3'd5);
fifo_cover_entrynum_4: cover property (~rst & number_of_current_entries = 3'd4);
fifo_cover_entrynum_3: cover property (~rst & number_of_current_entries = 3'd3);
fifo_cover_entrynum_2: cover property (~rst & number_of_current_entries = 3'd2);
fifo_cover_entrynum_1: cover property (~rst & number_of_current_entries = 3'd1);
fifo_cover_entrynum_0: cover property (~rst & number_of_current_entries = 3'd0);

endmodule
