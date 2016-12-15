

clean:
	cd $(SIM_ROOT)/.. && rm -rf *.jou
	cd $(SIM_ROOT)/.. && rm -rf .cxl.vcs_mx.version
	cd $(SIM_ROOT)/.. && rm -rf compile_simlib.log
	cd $(SIM_ROOT)/.. && rm -rf synopsys_sim.setup
	cd $(SIM_ROOT)/.. && rm -rf vivado.log
	cd $(SIM_DIR) && rm -rf AN.DB
	cd $(SIM_DIR) && rm -rf csrc
	cd $(SIM_DIR) && rm -rf simv*
	cd $(SIM_DIR) && rm -rf ucli.key
	cd $(SIM_DIR) && rm -rf vc_hdrs.h
	cd $(SIM_DIR) && rm -rf *.log
	cd $(SIM_DIR) && rm -rf *.vpd

