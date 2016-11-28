// General settings
-Xcheck_p1800_2009=char
+systemverilogext+.sv
+libext+.sv
+libext+.v

+define+PCIE_X16
+define+USE_GTE4

# uvm
-f $FILES_DIR/uvm_pkg.f

+incdir+$SCRIPTS_DIR/../sv

// RTL

-f $FILES_DIR/dut_venom_cl.f
-f $SCRIPTS_DIR/ddr_files.f

+define+PCIE_X16 +define+DW_ALIGNED

// TB
-f $SCRIPTS_DIR/hmc_model.f

-f $SCRIPTS_DIR/venom_tb_files.f
