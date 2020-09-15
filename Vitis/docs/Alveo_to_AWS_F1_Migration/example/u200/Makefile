TARGET := hw

build: xclbin host

run: build
	./host ./vadd.xclbin

vadd.xo: ../src/vadd.cpp
	v++ -c -g -t $(TARGET) -R 1 -k vadd \
		--profile_kernel data:all:all:all \
		--profile_kernel stall:all:all:all \
		--save-temps \
		--temp_dir ./temp_dir \
		--report_dir ./report_dir \
		--log_dir ./log_dir \
		--config ./options.cfg \
		-I../src \
		../src/vadd.cpp \
		-o ./vadd.xo

vadd.xclbin: vadd.xo
	v++ -l -g -t $(TARGET) -R 1 \
		--profile_kernel data:all:all:all \
		--profile_kernel stall:all:all:all \
		--temp_dir ./temp_dir \
		--report_dir ./report_dir \
		--log_dir ./log_dir \
		--config ./options.cfg \
		-I../src \
		vadd.xo \
		-o vadd.xclbin

host: ../src/host.cpp  ../src/host.hpp
	g++ -D__USE_XOPEN2K8 \
		-I$(XILINX_XRT)/include/ \
		-I./src \
		-O3 -Wall -fmessage-length=0 -std=c++11\
		../src/host.cpp \
		-L$(XILINX_XRT)/lib/ \
		-lxilinxopencl -lpthread -lrt \
		-o ./host

xclbin: vadd.xclbin

xo: vadd.xo

clean:
	rm -rf temp_dir log_dir report_dir *log host vadd.* *.csv *summary .run .Xil vitis* xclbin *.protoinst *.wdb *.wcfg
