
# TODO:
# Add check if CL_DIR and HDK_SHELL_DIR directories exist
# Add check if /build and /build/src_port_encryption directories exist
# Add check if the vivado_keyfile exist

set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)
set CL_DIR $::env(CL_DIR)

set TARGET_DIR $CL_DIR/build/src_post_encryption
set UNUSED_TEMPLATES_DIR $HDK_SHELL_DIR/design/interfaces

# Remove any previously encrypted files, that may no longer be used
exec rm -f $TARGET_DIR/*

#---- Developr would replace this section with design files ----

## Change file names and paths below to reflect your CL area.  DO NOT include AWS RTL files.
file copy -force $CL_DIR/design/YOUR_HEADER_FILES_HERE.vh		$TARGET_DIR
file copy -force $CL_DIR/design/YOUR_SOURCE_FILES_HERE.sv 			$TARGET_DIR 

# remove any of the next rows if u plan to use the corresponding interfaces

file copy -force $UNUSED_TEMPLATES_DIR/unused_apppf_irq_template.inc 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_aurora_template.inc 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_ddr_a_b_d_template.inc 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_cl_sda_template.inc 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_sh_ocl_template.inc 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_ddr_c_template.inc 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_dma_pcis_template.inc 	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_hmc_template.inc		$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_pcim_template.inc		$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_sh_bar1_template.inc	$TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_flr_template.inc      	$TARGET_DIR

# Make sure files have write permissions for the encryption
exec chmod +w {*}[glob $TARGET_DIR/*] 

encrypt -k $HDK_SHELL_DIR/build/scripts/vivado_keyfile.txt -lang verilog [glob $TARGET_DIR/*.*]

#---- End of section replaced by Developr ---
