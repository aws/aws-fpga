#!/usr/bin/bash -ex

cd $SDK_DIR/tests
rm -rf fio_dma_tools_original
aws s3 cp s3://aws-fpga-jenkins-testing/fio_dma_tools/ fio_dma_tools_original/ --recursive
cd fio_dma_tools_original
rm -rf xdma_v2017_1/
cd fio
chmod +x configure
./configure
make
mv fio ../scripts
cd ..
rm -rf fio
cd ..
aws s3 rm s3://aws-fpga-jenkins-testing/fio_dma_tools_compiled --recursive
aws s3 cp fio_dma_tools_original/ s3://aws-fpga-jenkins-testing/fio_dma_tools_compiled --recursive
rm -rf fio_dma_tools_original/
