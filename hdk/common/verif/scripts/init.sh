#!/bin/sh

vivado -mode batch -source $HDK_COMMON_DIR/verif/scripts/init.tcl

cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/arch_defines.v              ./models/ddr4_model/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/arch_package.sv              ./models/ddr4_model/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/ddr4_model.sv               ./models/ddr4_model/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/ddr4_sdram_model_wrapper.sv ./models/ddr4_model/
#cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/dimm_interface.sv           ./models/ddr4_model/
#cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/dimm_subtest.vh             ./models/ddr4_model/
#cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/dimm.vh                     ./models/ddr4_model/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/interface.sv                ./models/ddr4_model/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/MemoryArray.sv              ./models/ddr4_model/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/proj_package.sv             ./models/ddr4_model/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/StateTableCore.sv           ./models/ddr4_model/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/StateTable.sv               ./models/ddr4_model/
#cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/subtest.vh                  ./models/ddr4_model/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/timing_tasks.sv             ./models/ddr4_model/

cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/ddr4_bi_delay.sv            ./models/ddr4_rdimm_wrapper/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/ddr4_db_delay_model.sv      ./models/ddr4_rdimm_wrapper/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/ddr4_db_dly_dir.sv          ./models/ddr4_rdimm_wrapper/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/ddr4_dimm.sv                ./models/ddr4_rdimm_wrapper/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/ddr4_dir_detect.sv          ./models/ddr4_rdimm_wrapper/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/ddr4_rank.sv                ./models/ddr4_rdimm_wrapper/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/ddr4_rcd_model.sv           ./models/ddr4_rdimm_wrapper/
cp tmp/tmp_ddr_ex/ddr4_core_ex/imports/ddr4_rdimm_wrapper.sv       ./models/ddr4_rdimm_wrapper/

cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/sys_clk_gen_ds.v   ./models/xilinx_task_pcie_x16/functional
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/sys_clk_gen.v      ./models/xilinx_task_pcie_x16/functional
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/xil_sig2pipe.v     ./models/xilinx_task_pcie_x16/functional
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/board_common.vh    ./models/xilinx_task_pcie_x16/functional
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/board.v            ./models/xilinx_task_pcie_x16/functional

cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/pcie_4_0_rp.v                 ./models/xilinx_task_pcie_x16/dsport
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/xilinx_pcie_uscale_rp.v       ./models/xilinx_task_pcie_x16/dsport
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/pci_exp_expect_tasks.vh       ./models/xilinx_task_pcie_x16/dsport
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/pci_exp_usrapp_cfg.v          ./models/xilinx_task_pcie_x16/dsport
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/pci_exp_usrapp_com.v          ./models/xilinx_task_pcie_x16/dsport
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/pci_exp_usrapp_rx.v           ./models/xilinx_task_pcie_x16/dsport
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/pci_exp_usrapp_tx.v           ./models/xilinx_task_pcie_x16/dsport
cp tmp/tmp_pci_ex/pcie4_uscale_plus_0_ex/imports/xp4_usp_smsw_model_core_top.v ./models/xilinx_task_pcie_x16/dsport

#rm -rf tmp
cd $HDK_COMMON_DIR/verif/models/
patch -s -p0 < $HDK_COMMON_DIR/verif/scripts/xilinx_task_pcie.patch
