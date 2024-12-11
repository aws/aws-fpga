if [ -z "$PLATFORM_REPO_PATHS" ]; then
    echo "[ERROR]   vitis_setup.sh must be sourced before running this script!"
    return 1
fi

function build_example_in_background {
    if [ ! -e "makefile_us_alveo.mk" ]; then
        echo "[ERROR]    The current directory does not contain a makefile! Exiting!"
        return 1
    fi

    nohup make build TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION &> hw_emu.out &

    sleep 180
}

function build_all_examples {
    local marker_file="makefile_us_alveo.mk"  # Using the makefile as the marker

    if [[ -z $AWS_FPGA_REPO_DIR ]]; then
        echo "[ERROR]    Please run 'source vitis_setup.sh' from the devkit root before running this command!"
    fi

    examples_root=$AWS_FPGA_REPO_DIR/vitis/examples/vitis_examples
    cd $examples_root

    for dir in $(find . -maxdepth 2 -type d); do
        if [[ -e $dir/$marker_file ]]; then
            cd $dir
            echo "Running hardware build and emulation in $dir"
            build_example_in_background
            cd $examples_root
        fi
    done

}
