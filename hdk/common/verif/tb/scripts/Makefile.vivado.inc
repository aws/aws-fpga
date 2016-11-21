

clean:
	cd $(SIM_DIR) && rm -rf .Xil
	cd $(SIM_DIR) && rm -rf xsim.dir
	cd $(SIM_DIR) && rm -rf *.log
	cd $(SIM_DIR) && rm -rf *.jou
	cd $(SIM_DIR) && rm -rf *.pb
	cd $(SIM_DIR) && rm -rf *.dat
	cd $(SIM_DIR) && rm -rf *.wdb

