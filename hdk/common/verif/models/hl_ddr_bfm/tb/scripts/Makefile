
#export LD_LIBRARY_PATH := $(DENALI)/lib:$(DENALI)/verilog:$(DENALI)/lib/vip_lib:$(CDN_VIP_ROOT)/specman/linux64:$(LD_LIBRARY_PATH)

export CDN_VIP_LIB_PATH := /tools/cadence/vipcat/11.30.031/tools/psui/lib
export SPECMAN_PATH     := $(CDN_VIP_ROOT)/packages:$(CDN_VIP_LIB_PATH)/64bit


#VCS installation
export VCS_HOME := /tools/synopsys/vcs-mx/K-2015.09-SP2

#CDN_VIP_ROOT:: Environment variable pointing to Cadence VIP installation
export CDN_VIP_ROOT := /tools/cadence/vipcat/11.30.031

#CDS_ARCH:: Platform for Cadence VIP libraries
#This is obtained from: ${CDN_VIP_ROOT}/bin/cds_plat
export CDS_ARCH := linux-x64

#DENALI:: Environment variable pointing to Cadence VIP base libraries
export DENALI := $(CDN_VIP_ROOT)/tools.lnx86/denali_64bit

#SPECMAN_PATH:: Environment variable dictating locations (and search order)
#for multiple Cadence VIP components: Virtual Machine, compiled libraries
export SPECMAN_PATH := $(CDN_VIP_ROOT)/packages:$(CDN_VIP_LIB_PATH)/64bit

#Additional components in ${PATH} to ensure necessary executables are available
export PATH := $(CDN_VIP_ROOT)/tools.lnx86/bin:$(VCS_HOME)/bin:$(PATH)

#Additional components in ${LD_LIBRARY_PATH} to ensure necessary libraries are available
#export LD_LIBRARY_PATH := $(CDN_VIP_ROOT)/psui/lib/64bit:$(DENALI)/verilog:$(CDN_VIP_ROOT)/tools.lnx86/lib/64bit:$(LD_LIBRARY_PATH)
export LD_LIBRARY_PATH := $(CDN_VIP_ROOT)/tools.lnx86/psui/lib/64bit:$(DENALI)/verilog:$(CDN_VIP_ROOT)/tools.lnx86/lib/64bit

#SPECMAN_PRE_COMMANDS:: Environment variable for Cadence VIP Virtual Machine initialization
export SPECMAN_PRE_COMMANDS := 

#UVC_MSI_MODE:: Environment variable for Cadence VIP Virtual Machine licensing 
#		(Variable value is irrelevant/Only the declaration is relevant) 
export UVC_MSI_MODE := 


all:
	@echo ${CDN_VIP_ROOT}
	@echo ${DENALI}
	@echo ${CDN_VIP_LIB_PATH}
	@echo ${CDS_ARCH}
	@echo ${LD_LIBRARY_PATH}
	@echo $(SPECMAN_PRE_COMMANDS)
	vcs -full64 -l simv.log -R -sverilog -debug_all \
	-Mupdate=1 +vpi -LDFLAGS -Wl,-E \
	-P ${CDN_VIP_ROOT}/specman/src/pli.tab \
	-top specman -top specman_wave \
	+define+DENALI_SV_VCS -lca -ntb_opts svp \
	+define+DENALI_UVM +define+VCS -ntb_opts uvm-1.1 \
	-CFLAGS '-DDENALI_SV_VCS=1 -I../ -I/usr/local/include -I${DENALI} -I${DENALI}/ddvapi -O2 -c' \
	-CFLAGS '-DCDN_UVC_USING_INTELLIGEN -DDSN_USE_DYNAMIC_C_INTERFACE' \
	-LDFLAGS '-rdynamic ${DENALI}/verilog/libcdnsv.so' \
	-P ${DENALI}/verilog/cdnsv.tab \
	-LDFLAGS '-rdynamic ${CDN_VIP_LIB_PATH}/64bit/libsn_uvc.so' \
	${CDN_VIP_ROOT}/specman/linux/64bit/libvcssv_sn_boot.so \
	+incdir+${DENALI}/ddvapi/sv \
	${DENALI}/ddvapi/sv/denaliMemSvIf.c \
	${DENALI}/ddvapi/sv/denaliMem.sv \
	${DENALI}/ddvapi/sv/denaliCdn_axiSvIf.c \
	${DENALI}/ddvapi/sv/denaliCdn_axi.sv \
	+incdir+${DENALI}/ddvapi/sv/uvm/cdn_axi \
	${DENALI}/ddvapi/sv/uvm/cdn_axi/cdnAxiUvmTop.sv \
	-top testbench \
	-timescale=1ns/10ps   \
	+define+CDN_AUTO_TEST \
	+incdir+/proj/awsip_work/winefred/fpga_instance/Chimera/verif/models/hl_ddr_bfm/tb/axi4 \
	+incdir+/proj/awsip_work/winefred/fpga_instance/Chimera/verif/models/hl_ddr_bfm/tb/using_config_object \
	/tools/cadence/installs/VIPCAT113/tools.lnx86/denali/ddvapi/sv/hdl_interfaces/cdn_axi/cdnAxi4Interface.sv \
	../../hl_ddr_bfm.sv \
	/proj/awsip_work/winefred/fpga_instance/Chimera/verif/models/hl_ddr_bfm/tb/sv/axi4UvmUserTop.sv \
	/proj/awsip_work/winefred/fpga_instance/Chimera/verif/models/hl_ddr_bfm/tb/sv/axi4UvmUserTb.sv \
	${CDN_VIP_LIB_PATH}/64bit/vcs_psui.sv \
	+UVM_TESTNAME=basicTest
