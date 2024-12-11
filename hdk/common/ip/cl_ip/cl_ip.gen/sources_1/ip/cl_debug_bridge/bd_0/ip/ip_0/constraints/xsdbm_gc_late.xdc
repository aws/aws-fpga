

set_false_path -quiet -to [get_cells -hierarchical -filter {NAME =~ "*BSCANID.u_xsdbm_id/ZERO_SLAVES.update_i_reg*"} -quiet]
set_false_path -quiet -to [get_cells -hierarchical -filter {NAME =~ "*BSCANID.u_xsdbm_id/ZERO_SLAVES.shift_i_reg*"} -quiet]
set_false_path -quiet -to [get_cells -hierarchical -filter {NAME =~ "*BSCANID.u_xsdbm_id/ZERO_SLAVES.sel_i_reg*"} -quiet]
set_false_path -quiet -to [get_cells -hierarchical -filter {NAME =~ "*BSCANID.u_xsdbm_id/ZERO_SLAVES.tdi_i_reg*"} -quiet]
set_false_path -quiet -to [get_cells -hierarchical -filter {NAME =~ "*BSCANID.u_xsdbm_id/ZERO_SLAVES.tms_i_reg*"} -quiet]
set_false_path -quiet -to [get_cells -hierarchical -filter {NAME =~ "*BSCANID.u_xsdbm_id/ZERO_SLAVES.capture_i_reg*"} -quiet]
set_false_path -quiet -to [get_cells -hierarchical -filter {NAME =~ "*BSCANID.u_xsdbm_id/ZERO_SLAVES.runtest_i_reg*"} -quiet]
set_false_path -quiet -to [get_cells -hierarchical -filter {NAME =~ "*BSCANID.u_xsdbm_id/ZERO_SLAVES.reset_i_reg*"} -quiet]
set_false_path -quiet -to [get_cells -hierarchical -filter {NAME =~ "*BSCANID.u_xsdbm_id/ZERO_SLAVES.bscanid_en_i_reg*"} -quiet]
set_false_path -quiet -to [get_cells -hierarchical -filter {NAME =~ "*BSCANID.u_xsdbm_id/ZERO_SLAVES.drck_i_reg*"} -quiet]

