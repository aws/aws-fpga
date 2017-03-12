
# TODO:
# Add check if CL_DIR and HDK_SHELL_DIR directories exist
# Add check if /build and /build/src_port_encryption directories exist
# Add check if the vivado_keyfile exist

set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)
set CL_DIR $::env(CL_DIR)

set TARGET_DIR $CL_DIR/build/src_post_encryption
set UNUSED_TEMPLATES_DIR $HDK_SHELL_DIR/design/interfaces

#---- Developr would replace this section with design files ----

## Change file names and paths below to reflect your CL area.  DO NOT include AWS RTL files.
file copy -force $CL_DIR/design/cl_hello_world_defines.vh		$TARGET_DIR
file copy -force $CL_DIR/design/cl_hello_world.sv 			$TARGET_DIR 
file copy -force $CL_DIR/../common/design/cl_common_defines.vh 		$TARGET_DIR 
file copy -force $UNUSED_TEMPLATES_DIR/unused_apppf_irq_template.vh 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_aurora_template.vh 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_cl_sda_template.vh 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_ddr_a_b_d_template.vh 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_ddr_c_template.vh 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_dma_pcis_template.vh 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_hmc_template.vh		$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_pcim_template.vh		$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_sh_bar1_template.vh	$TARGET_DIR

# Make sure files have write permissions for the encryption
exec chmod +w {*}[glob ../src_post_encryption/*.*v*]

encrypt -k $HDK_SHELL_DIR/build/scripts/vivado_keyfile.txt -lang verilog \
$TARGET_DIR/cl_hello_world_defines.vh \
$TARGET_DIR/cl_common_defines.vh \
$TARGET_DIR/cl_hello_world.sv \
$TARGET_DIR/unused_apppf_irq_template.vh \
$TARGET_DIR/unused_aurora_template.vh \
$TARGET_DIR/unused_cl_sda_template.vh \
$TARGET_DIR/unused_ddr_a_b_d_template.vh \
$TARGET_DIR/unused_ddr_c_template.vh \
$TARGET_DIR/unused_dma_pcis_template.vh \
$TARGET_DIR/unused_hmc_template.vh \
$TARGET_DIR/unused_pcim_template.vh \
$TARGET_DIR/unused_sh_bar1_template.vh


#---- End of section replaced by Developr ---
