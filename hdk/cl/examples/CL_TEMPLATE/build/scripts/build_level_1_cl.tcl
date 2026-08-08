if { [info exists ::env(HDK_SHELL_DIR)] } {
  set common_build_level_1 [file join $::env(HDK_SHELL_DIR) build scripts build_level_1_cl.tcl]
} else {
  error "HDK_SHELL_DIR not set. Please source hdk_setup.sh before sourcing build_level_1_cl.tcl."
}

source $common_build_level_1
