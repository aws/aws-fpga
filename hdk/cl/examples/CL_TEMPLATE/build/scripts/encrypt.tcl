if { [info exists ::env(HDK_SHELL_DIR)] } {
  set common_build_level_1 [file join $::env(HDK_SHELL_DIR) build scripts encrypt.tcl]
} else {
  error "HDK_SHELL_DIR not set. Please source hdk_setup.sh before sourcing encrypt.tcl."
}

source $common_build_level_1
