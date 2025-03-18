#include <fpga_dma_mem.h>

#include <fcntl.h>
#include <hal/fpga_common.h>
#include <stdio.h>
#include <sys/mman.h>
#include <utils/log.h>

#define __USE_LARGEFILE64
#include <sys/types.h>
#include <unistd.h>

#define BIT(b)          (1LL << (b))

/* pagemap bits */
#define PAGE_FRAME_NUM  (BIT(55) - 1)

#define PAGE_SHIFT      12
#define PAGE_SIZE       (1 << PAGE_SHIFT)
#define PAGE_MASK       (PAGE_SIZE - 1)

static int get_pagemap(uint64_t page_frame_number, uint64_t* pagemap) {
  int ret = FPGA_ERR_FAIL;
  fail_on_with_code(pagemap == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "page_map is NULL");

  char pagemap_file_path[128];
  snprintf(pagemap_file_path, sizeof(pagemap_file_path), "/proc/%d/pagemap", getpid());

  int fd = open(pagemap_file_path, 0);
  fail_on_with_code(fd == -1, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "open(%s) failed: %m", pagemap_file_path);

  lseek64(fd, page_frame_number * 8, SEEK_SET);
  size_t bytes_read = read(fd, pagemap, sizeof(*pagemap));
  fail_on_with_code( bytes_read != sizeof(*pagemap), cleanup, ret, FPGA_ERR_SOFTWARE_PROBLEM, "read(%s) failed: %m", pagemap_file_path);
  return FPGA_ERR_OK;

cleanup:
  close(fd);

err:
  return ret;
}

static int get_physical_address(void* virtual_address, uint64_t* physical_address) {
  int ret = FPGA_ERR_FAIL;
  fail_on_with_code(virtual_address == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "virtual_address is NULL");

  uint64_t virtual_page_frame_number = ((uintptr_t) virtual_address) >> PAGE_SHIFT;
  uint64_t pagemap;
  ret = get_pagemap(virtual_page_frame_number, &pagemap);
  fail_on_with_code(ret != FPGA_ERR_OK, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "get_pagemap failed");

  uint64_t physical_page_frame_number = (uintptr_t) pagemap & PAGE_FRAME_NUM;
  uint64_t offset = ((uintptr_t) virtual_address) & PAGE_MASK;
  *physical_address = (physical_page_frame_number * PAGE_SIZE) | offset;

err:
  return ret;
}

static int map_page(int fd, size_t size_bytes, uint64_t* virtual_address, uint64_t* physical_address) {
  int ret = 0;
  int prot = PROT_READ | PROT_WRITE;
  int flags = MAP_PRIVATE | MAP_ANONYMOUS;

  void *va = mmap(NULL, size_bytes, prot, flags, fd, 0);
  fail_on_with_code(va == MAP_FAILED, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "mmap failed");

  *virtual_address = (uint64_t) va;
  *(uint32_t *) va = 0;

  ret = mlockall(MCL_CURRENT);
  fail_on_with_code(ret != FPGA_ERR_OK, cleanup, ret, FPGA_ERR_SOFTWARE_PROBLEM, "mlockall failed");

  ret = get_physical_address(va, physical_address);
  fail_on_with_code(ret != FPGA_ERR_OK, cleanup, ret, FPGA_ERR_SOFTWARE_PROBLEM, "get_physical_address failed");

err:
  return ret;
cleanup:
  munmap(va, size_bytes);
  return ret;
}

int fpga_dma_mem_alloc(int fd, size_t size_bytes, uint64_t* virtual_address, uint64_t* physical_address) {
  int ret = 0;
  fail_on_with_code(virtual_address == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "virtual_address is NULL");
  fail_on_with_code(physical_address == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "physical_address is NULL");
  fail_on_with_code(size_bytes == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "size_bytes is 0");

  ret = map_page(fd, size_bytes, virtual_address, physical_address);
  fail_on_with_code(ret != FPGA_ERR_OK, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "map_page failed");

  log_info("fpga_dma_mem_alloc: size_bytes = %zu, virtual_address = 0x%lx, physical_address = 0x%lx\n", size_bytes, *virtual_address, *physical_address);

err:
  return ret;
}

int fpga_dma_mem_dealloc(uint64_t* virtual_address, size_t size_bytes) {
  int ret = FPGA_ERR_FAIL;
  fail_on_with_code(virtual_address == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "virtual_address is NULL");
  fail_on_with_code(size_bytes == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "size_bytes is 0");

  ret = munmap((void *) *virtual_address, size_bytes);
  fail_on_with_code(ret != FPGA_ERR_OK, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "munmap failed");

  *virtual_address = 0;
err:
  return ret;
}
