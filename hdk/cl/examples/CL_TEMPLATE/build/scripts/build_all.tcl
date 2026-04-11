if { [info exists ::env(HDK_SHELL_DIR)] } {
  set common_build_all [file join $::env(HDK_SHELL_DIR) build scripts build_all.tcl]
} else {
  error "HDK_SHELL_DIR not set. Please source hdk_setup.sh before sourcing build_all.tcl."
}

source $common_build_all
