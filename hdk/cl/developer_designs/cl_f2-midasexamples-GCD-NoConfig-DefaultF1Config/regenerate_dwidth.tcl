# Force regenerate axi_dwidth_converter_0 to fix internal multi-driver issue

set CL_DIR [pwd]/../..
set F2_PART "xcvu47p-fsvh2892-2-e"

puts "Regenerating axi_dwidth_converter_0 IP..."

# Create temporary project  
create_project -in_memory -part $F2_PART

# Read the IP
set xci_file "$CL_DIR/ip/axi_dwidth_converter_0/axi_dwidth_converter_0.xci"
read_ip $xci_file

# Reset/upgrade the IP
set ip_name [get_property NAME [get_ips]]
puts "IP: $ip_name"

# Force regenerate all outputs
puts "Force regenerating all output products..."
generate_target all [get_ips $ip_name] -force

# Synthesize
puts "Synthesizing..."
synth_ip [get_ips $ip_name] -force

puts "Done regenerating $ip_name"
close_project

