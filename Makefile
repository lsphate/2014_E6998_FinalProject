###################################################################################
#               Copyright 2006-2013 Mentor Graphics Corporation
#                            All Rights Reserved.
#               THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY
#             INFORMATION WHICH IS THE PROPERTY OF MENTOR GRAPHICS 
#         CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
###################################################################################
# V10.2 Formal Quick Start Tutorial
###################################################################################
run: clean compile formal debug

###### Define Variables ###########################################################
VLIB = ${QHOME}/modeltech/plat/vlib
VMAP = ${QHOME}/modeltech/plat/vmap
VLOG = ${QHOME}/modeltech/plat/vlog

#DUT = ./src/svlog/fifo.sv ./src/svlog/fifo_wrapper.sv
DUT = ./src/svlog/fifo_with_error_checker.sv
SVA_BIND = ./src/assertions/sva_bind_fifo.sv
SVA_CHECK = ./src/assertions/sva_fifo.sv

###### Compile Design #############################################################
compile:
	$(VLIB) work
	$(VMAP) work work
#	$(VLOG) ./src/vlog/wb_arbiter.v -pslfile ./src/assertions/arbiter_vlog.psl
#	$(VLOG) -sv -mfcu -cuname my_bind_sva \
		./src/assertions/sva_bind.sv ./src/assertions/sva_arbiter.sv
#	$(VLOG) -sv -mfcu -cuname my_bind_ovl \
		./src/assertions/ovl_bind.sv ./src/assertions/ovl_arbiter.sv \
		+libext+.v+.sv -y ${QHOME}/share/assertion_lib/OVL/verilog \
		+incdir+${QHOME}/share/assertion_lib/OVL/verilog \
		+define+OVL_SVA+OVL_ASSERT_ON+OVL_COVER_ON+OVL_XCHECK_OFF
#	$(VLOG) -sv $(DUT) \
		+libext+.v+.sv -y ${QHOME}/share/assertion_lib/OVL/verilog \
		+incdir+${QHOME}/share/assertion_lib/OVL/verilog \
		+define+OVL_SVA+OVL_ASSERT_ON+OVL_COVER_ON+OVL_XCHECK_OFF
	$(VLOG) -sv $(DUT)

###### Run Formal Analysis ########################################################
formal:
#	qformal -c -od Output_Results -do "\
		do qs_files/directives.tcl; \
		formal compile -d wb_arbiter -cuname my_bind_sva my_bind_ovl \
			-target_cover_statements; \
		formal verify -init qs_files/wb_arbiter.init -effort high; \
		exit"
	qformal -c -od Output_Results -do "\
		do qs_files/directives.tcl; \
		formal compile -d fifo \
			-target_cover_statements; \
		formal verify -init qs_files/fifo.init -effort high; \
		exit"

###### Debug Results ##############################################################
debug: 
	qformal Output_Results/formal_verify.db &

###### Clean Data #################################################################
clean:
	qformal_clean
	\rm -rf work modelsim.ini *.wlf *.log replay* transcript *.db
	\rm -rf Output_Results *.tcl 

###################################################################################
# Regressions 
###################################################################################
REGRESS_FILE_LIST = \
	Output_Results/formal_property.rpt \
	Output_Results/formal_verify.rpt

regression: clean compile formal
	@rm -f regress_file_list
	@echo "# This file was generated by make" > regress_file_list
	@/bin/ls -1 $(REGRESS_FILE_LIST) >> regress_file_list
	@chmod -w regress_file_list
