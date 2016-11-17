#!/bin/csh -f
    #Step 1. Create cdn_vip_env_ncsim_sv_uvm.csh with environment setup commands
    #Note: NCSIM Compiled libraries path to be provided + libraries need to be installed
${CDN_VIP_ROOT}/bin/cdn_vip_setup_env -cdnautotest -s ncsim_3s -cdn_vip_root ${CDN_VIP_ROOT} -m sv_uvm -csh -cdn_vip_lib vip_lib -i axi
    #Step 2. Complete environment setup by executing generated shell commands
source cdn_vip_env_ncsim_sv_uvm.csh

    #Step 3. Create cdn_vip_run_ncsim_sv_uvm.sh with simulator comands
    #Note: CDN_VIP_ROOT environment variable guaranteed to be available after Step 2
${CDN_VIP_ROOT}/bin/cdn_vip_setup_example -s ncsim_3s -e ${CDN_VIP_ROOT}/tools/denali/ddvapi/sv/uvm/cdn_axi/examples/using_config_object/axi3 -m sv_uvm -cdn_vip_lib vip_lib -cdnautotest -cdnsvlib
    #Step 4. Execute generated script with compile/simulate commands (also doable by -r option to cdn_vip_setup_example)
./cdn_vip_run_ncsim_sv_uvm.sh

