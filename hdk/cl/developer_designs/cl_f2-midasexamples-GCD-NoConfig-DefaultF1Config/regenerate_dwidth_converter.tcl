# Regenerate axi_dwidth_converter_0 IP fresh for F2 part

set F2_PART "xcvu47p-fsvh2892-2-e"
set IP_DIR "/home/ubuntu/chipyard/sims/firesim/platforms/f2/aws-fpga-firesim-f2/hdk/cl/developer_designs/cl_f2-midasexamples-GCD-NoConfig-DefaultF1Config/ip"
set IP_NAME "axi_dwidth_converter_0"

puts "\n===================================================="
puts "Regenerating $IP_NAME for F2 part: $F2_PART"
puts "====================================================\n"

# Create temporary project
create_project -in_memory -part $F2_PART

# Create the IP from catalog
create_ip -name axi_dwidth_converter -vendor xilinx.com -library ip -version 2.1 -module_name $IP_NAME -dir $IP_DIR

# Configure the IP
set_property -dict [list \
  CONFIG.SI_DATA_WIDTH {64} \
  CONFIG.MI_DATA_WIDTH {512} \
  CONFIG.ADDR_WIDTH {64} \
  CONFIG.SI_ID_WIDTH {16} \
  CONFIG.ACLK_ASYNC {0} \
  CONFIG.FIFO_MODE {1} \
] [get_ips $IP_NAME]

# Generate all output products
puts "Generating output products..."
generate_target all [get_ips $IP_NAME]

# Synthesize
puts "Synthesizing IP..."
synth_ip [get_ips $IP_NAME]

puts "\n✓ IP regenerated successfully!"

close_project

