

clean:
	cd $(SIM_ROOT)/.. && rm -rf modelsim.ini
	cd $(SIM_ROOT)/.. && rm -rf *.log
	cd $(SIM_ROOT)/.. && rm -rf *.jou
	cd $(SIM_ROOT)/.. && rm -rf .cxl.questasim.version
	cd $(SIM_ROOT)/.. && rm -rf compile_simlib.log
	cd $(SIM_ROOT)/.. && rm -rf vivado.log
	cd $(SIM_DIR) && rm -rf work
	cd $(SIM_DIR) && rm -rf transcript

