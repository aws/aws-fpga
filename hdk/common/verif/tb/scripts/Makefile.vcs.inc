

clean:
	cd $(SIM_DIR) && rm -rf AN.DB
	cd $(SIM_DIR) && rm -rf csrc
	cd $(SIM_DIR) && rm -rf simv*
	cd $(SIM_DIR) && rm -rf ucli.key
	cd $(SIM_DIR) && rm -rf vc_hdrs.h
	cd $(SIM_DIR) && rm -rf *.log
	cd $(SIM_DIR) && rm -rf *.vpd

