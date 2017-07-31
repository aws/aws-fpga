# Definitional proc to organize widgets for parameters.
proc init_gui { IPINST } {
  ipgui::add_param $IPINST -name "Component_Name"
  #Adding Page
  set Page_0 [ipgui::add_page $IPINST -name "Page 0"]
  set interfaces_group   [ipgui::add_group $IPINST -parent $Page_0 -name {Enable IP Interfaces} -layout vertical] 
  set clock_group [ipgui::add_group $IPINST -parent $Page_0 -name {Clock Signals} -layout vertical] 
  set id_group    [ipgui::add_group $IPINST -parent $Page_0 -name {CL Partition ID} -layout vertical] 
  set advanced    [ipgui::add_group $IPINST -parent $Page_0 -name {Advanced} -layout vertical] 
  set DDR_A_PRESENT       [ipgui::add_param $IPINST -name "DDR_A_PRESENT"         -parent ${interfaces_group} -widget checkBox     ]
  set DDR_B_PRESENT       [ipgui::add_param $IPINST -name "DDR_B_PRESENT"         -parent ${interfaces_group} -widget checkBox     ]
  set DDR_C_PRESENT       [ipgui::add_param $IPINST -name "DDR_C_PRESENT"         -parent ${interfaces_group} -widget checkBox     ]
  set DDR_D_PRESENT       [ipgui::add_param $IPINST -name "DDR_D_PRESENT"         -parent ${interfaces_group} -widget checkBox     ]
  set PCIS_PRESENT        [ipgui::add_param $IPINST -name "PCIS_PRESENT"          -parent ${interfaces_group} -widget checkBox     ]
  set PCIM_PRESENT        [ipgui::add_param $IPINST -name "PCIM_PRESENT"          -parent ${interfaces_group} -widget checkBox         ]
  set SDA_PRESENT         [ipgui::add_param $IPINST -name "SDA_PRESENT"           -parent ${interfaces_group} -widget checkBox     ]
  set OCL_PRESENT         [ipgui::add_param $IPINST -name "OCL_PRESENT"           -parent ${interfaces_group} -widget checkBox     ]
  set BAR1_PRESENT        [ipgui::add_param $IPINST -name "BAR1_PRESENT"          -parent ${interfaces_group} -widget checkBox     ]
  set AUX_PRESENT         [ipgui::add_param $IPINST -name "AUX_PRESENT"           -parent ${interfaces_group} -widget checkBox     ]
  set NUM_A_CLOCKS        [ipgui::add_param $IPINST -name "NUM_A_CLOCKS"          -parent ${clock_group} -widget comboBox    ]
  set NUM_B_CLOCKS        [ipgui::add_param $IPINST -name "NUM_B_CLOCKS"          -parent ${clock_group} -widget comboBox    ]
  set NUM_C_CLOCKS        [ipgui::add_param $IPINST -name "NUM_C_CLOCKS"          -parent ${clock_group} -widget comboBox    ]
  set CLOCK_A_RECIPE      [ipgui::add_param $IPINST -name "CLOCK_A_RECIPE"        -parent ${clock_group} -widget comboBox  ]
    ipgui::add_indent $IPINST -parent ${clock_group}
  set CLOCK_A0_FREQ       [ipgui::add_param $IPINST -name "CLOCK_A0_FREQ"         -parent ${clock_group}                    ]
    ipgui::add_indent $IPINST -parent ${clock_group}
  set CLOCK_A1_FREQ       [ipgui::add_param $IPINST -name "CLOCK_A1_FREQ"         -parent ${clock_group}                    ]
    ipgui::add_indent $IPINST -parent ${clock_group}
  set CLOCK_A2_FREQ       [ipgui::add_param $IPINST -name "CLOCK_A2_FREQ"         -parent ${clock_group}                    ]
    ipgui::add_indent $IPINST -parent ${clock_group}
  set CLOCK_A3_FREQ       [ipgui::add_param $IPINST -name "CLOCK_A3_FREQ"         -parent ${clock_group}                    ]
  set CLOCK_B_RECIPE      [ipgui::add_param $IPINST -name "CLOCK_B_RECIPE"        -parent ${clock_group} -widget comboBox  ]
    ipgui::add_indent $IPINST -parent ${clock_group}
  set CLOCK_B0_FREQ       [ipgui::add_param $IPINST -name "CLOCK_B0_FREQ"         -parent ${clock_group}                    ]
    ipgui::add_indent $IPINST -parent ${clock_group}
  set CLOCK_B1_FREQ       [ipgui::add_param $IPINST -name "CLOCK_B1_FREQ"         -parent ${clock_group}                    ]
  set CLOCK_C_RECIPE      [ipgui::add_param $IPINST -name "CLOCK_C_RECIPE"        -parent ${clock_group} -widget comboBox  ]
    ipgui::add_indent $IPINST -parent ${clock_group}
  set CLOCK_C0_FREQ       [ipgui::add_param $IPINST -name "CLOCK_C0_FREQ"         -parent ${clock_group}                    ]
    ipgui::add_indent $IPINST -parent ${clock_group}
  set CLOCK_C1_FREQ       [ipgui::add_param $IPINST -name "CLOCK_C1_FREQ"         -parent ${clock_group}                    ]
  set VENDOR_ID           [ipgui::add_param $IPINST -name "VENDOR_ID"             -parent ${id_group}                           ]
  set DEVICE_ID           [ipgui::add_param $IPINST -name "DEVICE_ID"             -parent ${id_group}                           ]
  set SUBSYSTEM_VENDOR_ID [ipgui::add_param $IPINST -name "SUBSYSTEM_VENDOR_ID"   -parent ${id_group}                 ]
  set SUBSYSTEM_ID        [ipgui::add_param $IPINST -name "SUBSYSTEM_ID"          -parent ${id_group}                        ]
  set SHELL_VERSION       [ipgui::add_param $IPINST -name "SHELL_VERSION"         -parent ${id_group}                             ]
  set NUM_STAGES_SCALAR   [ipgui::add_param $IPINST -name "NUM_STAGES_SCALAR"     -parent ${advanced} -widget comboBox    ]
  
#  set_property tooltip "" $DDR_A_PRESENT      
#  set_property tooltip "" $DDR_B_PRESENT      
#  set_property tooltip "" $DDR_C_PRESENT      
#  set_property tooltip "" $DDR_D_PRESENT      
  set_property tooltip "Inbound PCIe Transactions from Shell to CL (AppPF BAR4)" $PCIS_PRESENT       
  set_property tooltip "Outbound PCIe Transactions from CL to Shell" $PCIM_PRESENT       
  set_property tooltip "MgmtPF PCIe BAR4 (4MB)" $SDA_PRESENT       
  set_property tooltip "AppPF PCIe BAR0 (32MB)" $OCL_PRESENT       
  set_property tooltip "AppPF PCIe BAR1 (2MB)" $BAR1_PRESENT       
  set_property tooltip "Enables irq_req, irq_ack, status_vdip, status_vled, flr_assert, flr_done, glcount, kernel_rst_n" $AUX_PRESENT       
  set_property tooltip "Clocks in Group A are edge-aligned and generated from the same PLL" $NUM_A_CLOCKS       
  set_property tooltip "Clocks in Group B are edge-aligned and generated from the same PLL" $NUM_B_CLOCKS       
  set_property tooltip "Clocks in Group C are edge-aligned and generated from the same PLL" $NUM_C_CLOCKS       
  set_property tooltip "" $CLOCK_A_RECIPE     
#  set_property tooltip "" $CLOCK_A0_FREQ      
#  set_property tooltip "" $CLOCK_A1_FREQ      
#  set_property tooltip "" $CLOCK_A2_FREQ      
#  set_property tooltip "" $CLOCK_A3_FREQ      
#  set_property tooltip "" $CLOCK_B_RECIPE     
#  set_property tooltip "" $CLOCK_B0_FREQ      
#  set_property tooltip "" $CLOCK_B1_FREQ      
#  set_property tooltip "" $CLOCK_C_RECIPE     
#  set_property tooltip "" $CLOCK_C0_FREQ      
#  set_property tooltip "" $CLOCK_C1_FREQ      
  set_property tooltip "Constant driven onto cl_sh_id0[15:0]" $VENDOR_ID          
  set_property tooltip "Constant driven onto cl_sh_id0[31:16]" $DEVICE_ID          
  set_property tooltip "Constant driven onto cl_sh_id1[15:0]" $SUBSYSTEM_VENDOR_ID
  set_property tooltip "Constant driven onto cl_sh_id1[31:16]" $SUBSYSTEM_ID       
  set_property tooltip "Version of the connected AWS Shell" $SHELL_VERSION       
  set_property tooltip "Pipelining of DDR statistics signals between DDR A/B/D and Shell" $NUM_STAGES_SCALAR  
}

proc update_PARAM_VALUE.NUM_STAGES_SCALAR { PARAM_VALUE.NUM_STAGES_SCALAR } {
	# Procedure called to update VENDOR_ID when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.VENDOR_ID { PARAM_VALUE.VENDOR_ID } {
	# Procedure called to update VENDOR_ID when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.DEVICE_ID { PARAM_VALUE.DEVICE_ID } {
	# Procedure called to update DEVICE_ID when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.SUBSYSTEM_VENDOR_ID { PARAM_VALUE.SUBSYSTEM_VENDOR_ID } {
	# Procedure called to update SUBSYSTEM_VENDOR_ID when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.SUBSYSTEM_ID { PARAM_VALUE.SUBSYSTEM_ID } {
	# Procedure called to update  when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.SHELL_VERSION { PARAM_VALUE.SHELL_VERSION } {
	# Procedure called to update  when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.CLOCK_A_RECIPE { PARAM_VALUE.CLOCK_A_RECIPE } {
	# Procedure called to update CLOCK_A_RECIPE when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.CLOCK_B_RECIPE { PARAM_VALUE.CLOCK_B_RECIPE PARAM_VALUE.NUM_B_CLOCKS } {
  set NUM_B_CLOCKS [get_property value ${PARAM_VALUE.NUM_B_CLOCKS}]
  if {$NUM_B_CLOCKS==0} {
    set_property range 0,0 ${PARAM_VALUE.CLOCK_B_RECIPE}
    set_property enabled false ${PARAM_VALUE.CLOCK_B_RECIPE}
  } else {
    set_property range 0,5 ${PARAM_VALUE.CLOCK_B_RECIPE}
    set_property enabled true ${PARAM_VALUE.CLOCK_B_RECIPE}
  }
}

proc update_PARAM_VALUE.CLOCK_C_RECIPE { PARAM_VALUE.CLOCK_C_RECIPE PARAM_VALUE.NUM_C_CLOCKS } {
  set NUM_C_CLOCKS [get_property value ${PARAM_VALUE.NUM_C_CLOCKS}]
  if {$NUM_C_CLOCKS==0} {
    set_property range 0,0 ${PARAM_VALUE.CLOCK_C_RECIPE}
    set_property enabled false ${PARAM_VALUE.CLOCK_C_RECIPE}
  } else {
    set_property range 0,3 ${PARAM_VALUE.CLOCK_C_RECIPE}
    set_property enabled true ${PARAM_VALUE.CLOCK_C_RECIPE}
  }
}

proc update_PARAM_VALUE.CLOCK_A0_FREQ { PARAM_VALUE.CLOCK_A0_FREQ PARAM_VALUE.CLOCK_A_RECIPE } {
  set clock_freq [list 125000000 250000000 15625000]
  set CLOCK_A_RECIPE [get_property value ${PARAM_VALUE.CLOCK_A_RECIPE}]
  set_property value [lindex $clock_freq $CLOCK_A_RECIPE] ${PARAM_VALUE.CLOCK_A0_FREQ}
  set_property enabled false ${PARAM_VALUE.CLOCK_A0_FREQ}
}

proc update_PARAM_VALUE.CLOCK_A1_FREQ { PARAM_VALUE.CLOCK_A1_FREQ PARAM_VALUE.CLOCK_A_RECIPE } {
  set clock_freq [list 62500000 125000000 15625000]
  set CLOCK_A_RECIPE [get_property value ${PARAM_VALUE.CLOCK_A_RECIPE}]
  set_property value [lindex $clock_freq $CLOCK_A_RECIPE] ${PARAM_VALUE.CLOCK_A1_FREQ}
  set_property enabled false ${PARAM_VALUE.CLOCK_A1_FREQ}
}

proc update_PARAM_VALUE.CLOCK_A2_FREQ { PARAM_VALUE.CLOCK_A2_FREQ PARAM_VALUE.CLOCK_A_RECIPE } {
  set clock_freq [list 187500000 375000000 125000000]
  set CLOCK_A_RECIPE [get_property value ${PARAM_VALUE.CLOCK_A_RECIPE}]
  set_property value [lindex $clock_freq $CLOCK_A_RECIPE] ${PARAM_VALUE.CLOCK_A2_FREQ}
  set_property enabled false ${PARAM_VALUE.CLOCK_A2_FREQ}
}

proc update_PARAM_VALUE.CLOCK_A3_FREQ { PARAM_VALUE.CLOCK_A3_FREQ PARAM_VALUE.CLOCK_A_RECIPE } {
  set clock_freq [list 250000000 500000000 62500000]
  set CLOCK_A_RECIPE [get_property value ${PARAM_VALUE.CLOCK_A_RECIPE}]
  set_property value [lindex $clock_freq $CLOCK_A_RECIPE] ${PARAM_VALUE.CLOCK_A3_FREQ}
  set_property enabled false ${PARAM_VALUE.CLOCK_A3_FREQ}
}

proc update_PARAM_VALUE.CLOCK_B0_FREQ { PARAM_VALUE.CLOCK_B0_FREQ PARAM_VALUE.CLOCK_B_RECIPE } {
  set clock_freq [list 250000000 125000000 450000000 250000000 300000000 400000000]
  set CLOCK_B_RECIPE [get_property value ${PARAM_VALUE.CLOCK_B_RECIPE}]
  set_property value [lindex $clock_freq $CLOCK_B_RECIPE] ${PARAM_VALUE.CLOCK_B0_FREQ}
  set_property enabled false ${PARAM_VALUE.CLOCK_B0_FREQ}
}

proc update_PARAM_VALUE.CLOCK_B1_FREQ { PARAM_VALUE.CLOCK_B1_FREQ PARAM_VALUE.CLOCK_B_RECIPE } {
  set clock_freq [list 125000000 62500000 225000000 62500000 75000000 100000000]
  set CLOCK_B_RECIPE [get_property value ${PARAM_VALUE.CLOCK_B_RECIPE}]
  set_property value [lindex $clock_freq $CLOCK_B_RECIPE] ${PARAM_VALUE.CLOCK_B1_FREQ}
  set_property enabled false ${PARAM_VALUE.CLOCK_B1_FREQ}
}

proc update_PARAM_VALUE.CLOCK_C0_FREQ { PARAM_VALUE.CLOCK_C0_FREQ PARAM_VALUE.CLOCK_C_RECIPE } {
  set clock_freq [list 300000000 150000000 75000000 200000000]
  set CLOCK_C_RECIPE [get_property value ${PARAM_VALUE.CLOCK_C_RECIPE}]
  set_property value [lindex $clock_freq $CLOCK_C_RECIPE] ${PARAM_VALUE.CLOCK_C0_FREQ}
  set_property enabled false ${PARAM_VALUE.CLOCK_C0_FREQ}
}

proc update_PARAM_VALUE.CLOCK_C1_FREQ { PARAM_VALUE.CLOCK_C1_FREQ PARAM_VALUE.CLOCK_C_RECIPE } {
  set clock_freq [list 400000000 200000000 100000000 266666666]
  set CLOCK_C_RECIPE [get_property value ${PARAM_VALUE.CLOCK_C_RECIPE}]
  set_property value [lindex $clock_freq $CLOCK_C_RECIPE] ${PARAM_VALUE.CLOCK_C1_FREQ}
  set_property enabled false ${PARAM_VALUE.CLOCK_C1_FREQ}
}

proc update_MODELPARAM_VALUE.C_CLOCK_A0_PERIOD { MODELPARAM_VALUE.C_CLOCK_A0_PERIOD PARAM_VALUE.CLOCK_A0_FREQ } {
  set freq [get_property value ${PARAM_VALUE.CLOCK_A0_FREQ}]
  set period [expr 1000000000.0 / $freq]
	set_property value $period ${MODELPARAM_VALUE.C_CLOCK_A0_PERIOD}
}

proc update_MODELPARAM_VALUE.C_CLOCK_B0_PERIOD { MODELPARAM_VALUE.C_CLOCK_B0_PERIOD PARAM_VALUE.CLOCK_B0_FREQ } {
  set freq [get_property value ${PARAM_VALUE.CLOCK_B0_FREQ}]
  set period [expr 1000000000.0 / $freq]
	set_property value $period ${MODELPARAM_VALUE.C_CLOCK_B0_PERIOD}
}

proc update_MODELPARAM_VALUE.C_CLOCK_C0_PERIOD { MODELPARAM_VALUE.C_CLOCK_C0_PERIOD PARAM_VALUE.CLOCK_C0_FREQ } {
  set freq [get_property value ${PARAM_VALUE.CLOCK_C0_FREQ}]
  set period [expr 1000000000.0 / $freq]
	set_property value $period ${MODELPARAM_VALUE.C_CLOCK_C0_PERIOD}
}

proc update_MODELPARAM_VALUE.C_CLOCK_A_RECIPE { MODELPARAM_VALUE.C_CLOCK_A_RECIPE PARAM_VALUE.CLOCK_A_RECIPE } {
	set_property value [get_property value ${PARAM_VALUE.CLOCK_A_RECIPE}] ${MODELPARAM_VALUE.C_CLOCK_A_RECIPE}
}

proc update_MODELPARAM_VALUE.C_CLOCK_B_RECIPE { MODELPARAM_VALUE.C_CLOCK_B_RECIPE PARAM_VALUE.CLOCK_B_RECIPE } {
	set_property value [get_property value ${PARAM_VALUE.CLOCK_B_RECIPE}] ${MODELPARAM_VALUE.C_CLOCK_B_RECIPE}
}

proc update_MODELPARAM_VALUE.C_CLOCK_C_RECIPE { MODELPARAM_VALUE.C_CLOCK_C_RECIPE PARAM_VALUE.CLOCK_C_RECIPE } {
	set_property value [get_property value ${PARAM_VALUE.CLOCK_C_RECIPE}] ${MODELPARAM_VALUE.C_CLOCK_C_RECIPE}
}

proc update_PARAM_VALUE.DDR_A_PRESENT { PARAM_VALUE.DDR_A_PRESENT } {
	# Procedure called to update DDR_A_PRESENT when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.DDR_B_PRESENT { PARAM_VALUE.DDR_B_PRESENT } {
	# Procedure called to update DDR_B_PRESENT when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.DDR_C_PRESENT { PARAM_VALUE.DDR_C_PRESENT } {
	# Procedure called to update DDR_B_PRESENT when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.DDR_D_PRESENT { PARAM_VALUE.DDR_D_PRESENT } {
	# Procedure called to update DDR_D_PRESENT when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.NUM_A_CLOCKS { PARAM_VALUE.NUM_A_CLOCKS } {
	# Procedure called to update NUM_A_CLOCKS when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.NUM_B_CLOCKS { PARAM_VALUE.NUM_B_CLOCKS } {
	# Procedure called to update NUM_B_CLOCKS when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.NUM_C_CLOCKS { PARAM_VALUE.NUM_C_CLOCKS } {
	# Procedure called to update NUM_C_CLOCKS when any of the dependent parameters in the arguments change
}

proc update_PARAM_VALUE.PCIM_PRESENT { PARAM_VALUE.PCIM_PRESENT } {
	# Procedure called to update PCIM_PRESENT when any of the dependent parameters in the arguments change
}

proc update_MODELPARAM_VALUE.C_DDR_A_PRESENT { MODELPARAM_VALUE.C_DDR_A_PRESENT PARAM_VALUE.DDR_A_PRESENT } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.DDR_A_PRESENT}] ${MODELPARAM_VALUE.C_DDR_A_PRESENT}
}

proc update_MODELPARAM_VALUE.C_DDR_B_PRESENT { MODELPARAM_VALUE.C_DDR_B_PRESENT PARAM_VALUE.DDR_B_PRESENT } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.DDR_B_PRESENT}] ${MODELPARAM_VALUE.C_DDR_B_PRESENT}
}

proc update_MODELPARAM_VALUE.C_DDR_D_PRESENT { MODELPARAM_VALUE.C_DDR_D_PRESENT PARAM_VALUE.DDR_D_PRESENT } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.DDR_D_PRESENT}] ${MODELPARAM_VALUE.C_DDR_D_PRESENT}
}

proc update_MODELPARAM_VALUE.C_NUM_A_CLOCKS { MODELPARAM_VALUE.C_NUM_A_CLOCKS PARAM_VALUE.NUM_A_CLOCKS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.NUM_A_CLOCKS}] ${MODELPARAM_VALUE.C_NUM_A_CLOCKS}
}

proc update_MODELPARAM_VALUE.C_NUM_B_CLOCKS { MODELPARAM_VALUE.C_NUM_B_CLOCKS PARAM_VALUE.NUM_B_CLOCKS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.NUM_B_CLOCKS}] ${MODELPARAM_VALUE.C_NUM_B_CLOCKS}
}

proc update_MODELPARAM_VALUE.C_NUM_C_CLOCKS { MODELPARAM_VALUE.C_NUM_C_CLOCKS PARAM_VALUE.NUM_C_CLOCKS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.NUM_C_CLOCKS}] ${MODELPARAM_VALUE.C_NUM_C_CLOCKS}
}

proc update_MODELPARAM_VALUE.C_PCIM_PRESENT { MODELPARAM_VALUE.C_PCIM_PRESENT PARAM_VALUE.PCIM_PRESENT } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.PCIM_PRESENT}] ${MODELPARAM_VALUE.C_PCIM_PRESENT}
}

proc update_MODELPARAM_VALUE.C_VENDOR_ID { MODELPARAM_VALUE.C_VENDOR_ID PARAM_VALUE.VENDOR_ID } {
	set_property value [get_property value ${PARAM_VALUE.VENDOR_ID}] ${MODELPARAM_VALUE.C_VENDOR_ID}
}

proc update_MODELPARAM_VALUE.C_DEVICE_ID { MODELPARAM_VALUE.C_DEVICE_ID PARAM_VALUE.DEVICE_ID } {
	set_property value [get_property value ${PARAM_VALUE.DEVICE_ID}] ${MODELPARAM_VALUE.C_DEVICE_ID}
}

proc update_MODELPARAM_VALUE.C_SUBSYSTEM_VENDOR_ID { MODELPARAM_VALUE.C_SUBSYSTEM_VENDOR_ID PARAM_VALUE.SUBSYSTEM_VENDOR_ID } {
	set_property value [get_property value ${PARAM_VALUE.SUBSYSTEM_VENDOR_ID}] ${MODELPARAM_VALUE.C_SUBSYSTEM_VENDOR_ID}
}

proc update_MODELPARAM_VALUE.C_SUBSYSTEM_ID { MODELPARAM_VALUE.C_SUBSYSTEM_ID PARAM_VALUE.SUBSYSTEM_ID } {
	set_property value [get_property value ${PARAM_VALUE.SUBSYSTEM_ID}] ${MODELPARAM_VALUE.C_SUBSYSTEM_ID}
}

proc update_MODELPARAM_VALUE.C_NUM_STAGES_SCALAR { MODELPARAM_VALUE.C_NUM_STAGES_SCALAR PARAM_VALUE.NUM_STAGES_SCALAR } {
	set_property value [get_property value ${PARAM_VALUE.NUM_STAGES_SCALAR}] ${MODELPARAM_VALUE.C_NUM_STAGES_SCALAR}
}

