#!/usr/bin/env bash


function remove_edma_driver_func {
    echo "INFO: Removing the edma driver"
    sudo rmmod edma-drv
    sudo rm -f /lib/modules/`uname -r`/edma-drv.ko
    sudo rm -f /etc/modules-load.d/edma.conf
}

function edma_driver_install_steps_func {
    echo "INFO: Running edma driver install steps"
    echo 'edma' | sudo tee -a /etc/modules-load.d/edma.conf
    pushd $WORKSPACE/sdk/linux_kernel_drivers/edma;
    make clean
    make
    sudo cp edma-drv.ko /lib/modules/`uname -r`/
    sudo depmod
    sudo modprobe edma-drv
    popd
}

# Function to install the edma drivers
function install_edma_driver_func {
    echo "INFO: Installing the edma drivers"

    # Check if the file exists
    if [ ! -f /etc/modules-load.d/edma.conf ]; then
        edma_driver_install_steps_func
    else
        echo "INFO: Edma driver is already installed."
        remove_edma_driver_func
        edma_driver_install_steps_func
    fi

    if [ $? -ne 0 ]; then
            echo "ERROR: Could not install EDMA Driver!";
            exit 1
    fi
}


# Process command line args
while [[ $# -gt 1 ]]
do
key="$1"

case $key in
    -t|--test)
    test="$2"
    shift # past argument
    ;;
    --install_edma_driver)
    install_edma_driver=1
    ;;
    *)
    echo -e >&2 "ERROR: Invalid option: $1\n"
    exit 1
    ;;
esac
shift # past argument or value
done

if [ ":$test" = ":" ]; then
    echo -e >&2 "ERROR: Invalid test: $test\n"
    exit 1
fi

if [ ! -d $WORKSPACE/hdk/cl/examples/$test ]; then
    echo -e >&2 "ERROR: The test passed in($test) does not exist at $WORKSPACE/hdk/cl/examples/$test!"
    exit 1
fi

pushd $WORKSPACE;

source $WORKSPACE/sdk_setup.sh;

pushd $WORKSPACE/hdk/cl/examples/$test;

test_afi=$(cat README.md | grep 'Pre-generated AGFI ID' | cut -d "|" -f 3)

echo "INFO: AFI from README: $test_afi";
echo "INFO: Clearing the FPGA first.";
sudo fpga-clear-local-image  -S 0

if [ $? -ne 0 ]; then
        echo -e >&2 "ERROR: Clearing FPGA failed!";
        exit 1
fi

echo "INFO: Sleeping 60 seconds"
sleep 60

echo "INFO: Loading AFI: $test_afi"
sudo fpga-load-local-image -S 0 -I $test_afi

if [ $? -ne 0 ]; then
        echo -e >&2 "ERROR: Loading FPGA with AFI failed!";
        exit 1
fi

echo "INFO: Sleeping 60 seconds"
sleep 60


echo "INFO: Checking AFI Load status"
describe_output=$(sudo fpga-describe-local-image -S 0 -R -H 2>&1 | grep ok)

echo "AFI Describe output: ${describe_output}"

if [ "${describe_output}" = "" ]; then
        echo -e >&2 "ERROR: AFI was not loaded"
        exit 1
fi

if [ "$install_edma_driver" -eq "1" ]; then
    set -x
    install_edma_driver_func
    set +x
fi

echo "INFO: Building runtime software"

pushd $WORKSPACE/hdk/cl/examples/$test/software/runtime;

sudo make -f Makefile SDK_DIR=$WORKSPACE/sdk

# Example test = cl_hello_world
# makefile makes test_hello_world, so removing cl_ from the string
test_obj_name=${test:3}

sudo ./test_$test_obj_name

if [ $? -ne 0 ]; then
        echo -e >&2 "ERROR: Non zero exit code after running the runtime example!";
        exit 1
fi
