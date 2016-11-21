set COMPLIB_DIR $::env(DESIGN_DIR)
append COMPLIB_DIR "/questa_complib"
puts $COMPLIB_DIR
compile_simlib -language all -dir $COMPLIB_DIR -simulator questa -library all -family  all
# compile_simlib -language all -dir $DESIGN_DIR -simulator questa -simulator_exec_path {$(QUESTA_HOME)/bin} -library all -family  all
