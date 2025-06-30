/*
 * Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may
 * not use this file except in compliance with the License. A copy of the
 * License is located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <sde_mgmt.h>
#include <sde_hw_ctrl.h>
#include <sde_dma_buffer.h>
#include <sde_mem.h>
#include <sde_utility.h>
#include <sde_hw_regs.h>

#include <utils/log.h>
#include <utils/lcd.h>

#include <fcntl.h>
#include <string.h>
#include <unistd.h>

#define DESC_WAIT_MAX_ITERS 1000000

struct sde_mgmt {
    struct sde_mem mem;
    struct sde_hw_ctrl hw_ctrl;
    struct sde_dma_buffer c2h_buffer;
    struct sde_dma_buffer h2c_buffer;

    enum SDE_EXAMPLE_DIR direction;

    uint32_t c2h_desc_consumed;
    uint32_t h2c_desc_consumed;
    uint32_t data_pattern;

    volatile struct c2h_status* c2h_status;
    volatile struct h2c_status* h2c_status;

    size_t md_read_index;
    volatile struct c2h_wb_metadata* metadata;
};

#define SDE_SLOT_MAX 8
static struct sde_mgmt priv_sde_mgmt[SDE_SLOT_MAX];

int sde_mgmt_init(int slot_id, enum SDE_EXAMPLE_DIR direction, size_t packet_size, enum SDE_BUFFER_LAYOUT layout) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];
  memset(sde_mgmt, 0, sizeof(*sde_mgmt));

  sde_mgmt->direction = direction;

  ret = sde_mem_init(&sde_mgmt->mem, layout, layout, sde_mgmt->direction, packet_size);
  fail_on(ret, err, "failed to init mem");

  ret = sde_hw_init(&sde_mgmt->hw_ctrl, slot_id);
  fail_on(ret, err, "failed to init hw_ctrl");

  uint64_t c2h_status_va;
  uint64_t c2h_status_pa;
  ret = sde_mem_get_status(&sde_mgmt->mem, SDE_SUBSYSTEM_C2H, &c2h_status_va, &c2h_status_pa);
  fail_on(ret, err, "failed to get c2h_status_va");

  sde_mgmt->c2h_status = (struct c2h_status*)c2h_status_va;

  ret = sde_dma_buffer_init(&sde_mgmt->c2h_buffer, layout, SDE_SUBSYSTEM_C2H, packet_size, &sde_mgmt->mem, &sde_mgmt->hw_ctrl);
  fail_on(ret, err, "failed to init c2h_buffer");

  uint64_t h2c_status_va;
  uint64_t h2c_status_pa;
  ret = sde_mem_get_status(&sde_mgmt->mem, SDE_SUBSYSTEM_H2C, &h2c_status_va, &h2c_status_pa);
  fail_on(ret, err, "failed to get h2c_status_va");

  sde_mgmt->h2c_status = (struct h2c_status*) h2c_status_va;

  ret = sde_dma_buffer_init(&sde_mgmt->h2c_buffer, layout, SDE_SUBSYSTEM_H2C, packet_size, &sde_mgmt->mem, &sde_mgmt->hw_ctrl);
  fail_on(ret, err, "failed to init h2c_buffer");

  uint64_t md_ring_va;
  uint64_t md_ring_pa;
  ret = sde_mem_get_metadata(&sde_mgmt->mem, SDE_SUBSYSTEM_C2H, &md_ring_va, &md_ring_pa);
  fail_on(ret, err, "failed to get md_ring_va");

  sde_mgmt->metadata = (struct c2h_wb_metadata*)(md_ring_va);

  sde_mgmt->data_pattern = START_DOUBLE_WORD;

err:
  return ret;
}

int sde_mgmt_init_and_cfg(int slot_id, enum SDE_EXAMPLE_DIR direction, size_t packet_size) {
  int ret = 0;

  ret = sde_mgmt_init(slot_id, direction, packet_size, SDE_BUFFER_LAYOUT_MULTI);
  fail_on(ret, err, "failed to init sde_mgmt");

  ret = sde_mgmt_reset(slot_id);
  fail_on(ret, err, "failed to reset sde_mgmt");

  ret = sde_mgmt_cfg(slot_id);
  fail_on(ret, err, "failed to cfg sde_mgmt");

err:
  return ret;
}

int sde_mgmt_close(int slot_id) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];

  ret |= sde_dma_buffer_close(&sde_mgmt->c2h_buffer);
  ret |= sde_dma_buffer_close(&sde_mgmt->h2c_buffer);
  ret |= sde_hw_close(&sde_mgmt->hw_ctrl);
  ret |= sde_mem_close(&sde_mgmt->mem);

  fail_on(ret, err, "failed to close elements of sde_mgmt");

err:
  return ret;
}

int sde_mgmt_reset(int slot_id) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];

  ret = sde_hw_reset(&sde_mgmt->hw_ctrl);
  fail_on(ret, err, "failed to reset hw_ctrl");

  sde_mgmt->c2h_status->status = 0;
  sde_mgmt->c2h_status->desc_limit = SDE_NUM_DESC;
  sde_mgmt->c2h_status->desc_completed = 0;
  sde_mgmt->c2h_status->pkt_completed = 0;
  sde_mgmt->c2h_status->meta_write = 0;

  sde_mgmt->h2c_status->status = 0;
  sde_mgmt->h2c_status->desc_limit = SDE_NUM_DESC;
  sde_mgmt->h2c_status->desc_completed = 0;
  sde_mgmt->h2c_status->pkt_completed = 0;

  sde_mgmt->md_read_index = 0;

err:
  return ret;
}

int sde_mgmt_check_status(int slot_id, enum SDE_SUBSYSTEM subsystem) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];

  uint32_t status = 0;
  if (subsystem == SDE_SUBSYSTEM_C2H) {
    status = sde_mgmt->c2h_status->status;
  } else if (subsystem == SDE_SUBSYSTEM_H2C) {
    status = sde_mgmt->h2c_status->status;
  }

  bool desc_error = SDE_GET_BITFIELD(STATUS_DESC_ERR, status) != 0;
  bool datamover_error = SDE_GET_BITFIELD(STATUS_DM_ERR, status) != 0;
  bool writeback_error = SDE_GET_BITFIELD(STATUS_WB_ERR, status) != 0;

  fail_on_with_code(desc_error, err, ret, SDE_STATUS_COUNTER_ERROR, "desc_error");
  fail_on_with_code(datamover_error, err, ret, SDE_STATUS_COUNTER_ERROR, "dm_error");
  fail_on_with_code(writeback_error, err, ret, SDE_STATUS_COUNTER_ERROR, "wb_error");

err:
  return ret;
}

int sde_mgmt_set_dma_buffers(int slot_id, enum SDE_SUBSYSTEM subsystem, struct sde_buffer* sde_buffers, size_t num_buffers) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);
  fail_on_with_code(num_buffers > SDE_NUM_DESC, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "num_buffers %ld is out of range", num_buffers);
  fail_on_with_code(num_buffers == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "num_buffers is 0");
  fail_on_with_code(sde_buffers == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "sde_buffers is NULL");

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];

  if (subsystem == SDE_SUBSYSTEM_C2H) {
    ret = sde_dma_buffer_set_dma_buffers(&sde_mgmt->c2h_buffer, sde_buffers, num_buffers);
    fail_on(ret, err, "failed to set c2h descriptors");
  } else if (subsystem == SDE_SUBSYSTEM_H2C) {
    ret = sde_dma_buffer_set_dma_buffers(&sde_mgmt->h2c_buffer, sde_buffers, num_buffers);
    fail_on(ret, err, "failed to set h2c descriptors");
  }

err:
  return ret;
}

static int sde_mgmt_cfg_c2h(struct sde_mgmt *sde_mgmt) {
  int ret = 0;

  uint64_t c2h_md_ring_va = 0;
  uint64_t c2h_md_ring_pa = 0;
  ret = sde_mem_get_metadata(&sde_mgmt->mem, SDE_SUBSYSTEM_C2H, &c2h_md_ring_va, &c2h_md_ring_pa);
  fail_on(ret, err, "failed to get md_ring va");

  size_t c2h_metadata_size = sizeof(struct c2h_wb_metadata);
  size_t c2h_metadata_ring_size = sde_aligned_size(c2h_metadata_size * C2H_NUM_MD_IN_RING, SDE_ALIGN);

  uint64_t c2h_status_va = 0;
  uint64_t c2h_status_pa = 0;
  ret = sde_mem_get_status(&sde_mgmt->mem, SDE_SUBSYSTEM_C2H, &c2h_status_va, &c2h_status_pa);
  fail_on(ret, err, "failed to get c2h_status_va");

  ret = sde_hw_cfg_c2h(&sde_mgmt->hw_ctrl, c2h_status_pa, c2h_md_ring_pa, c2h_metadata_ring_size);
  fail_on(ret, err, "failed to configure c2h");

err:
  return ret;
}

static int sde_mgmt_cfg_h2c(struct sde_mgmt *sde_mgmt) {
  int ret = 0;

  uint64_t h2c_status_va = 0;
  uint64_t h2c_status_pa = 0;
  ret = sde_mem_get_status(&sde_mgmt->mem, SDE_SUBSYSTEM_H2C, &h2c_status_va, &h2c_status_pa);
  fail_on(ret, err, "failed to get h2c_status_va");

  ret = sde_hw_cfg_h2c(&sde_mgmt->hw_ctrl, h2c_status_pa);
  fail_on(ret, err, "failed to configure h2c");

err:
  return ret;
}

static int sde_mgmt_cfg_packets(struct sde_mgmt *sde_mgmt) {
  int ret = 0;

  struct sde_dma_buffer *buffer = NULL;
  if (sde_mgmt->direction != SDE_EXAMPLE_DIR_H2C) {
    buffer = &sde_mgmt->c2h_buffer;
    ret = sde_dma_init_desc_buffer(buffer);
    fail_on(ret, err, "failed to init desc buffer");
  }

  if (sde_mgmt->direction != SDE_EXAMPLE_DIR_C2H) {
    buffer = &sde_mgmt->h2c_buffer;
    ret = sde_dma_init_desc_buffer(buffer);
    fail_on(ret, err, "failed to init desc buffer");
  }

err:
  return ret;
}

static int sde_mgmt_cfg_c2h_atg(struct sde_mgmt *sde_mgmt) {
  int ret = 0;

  bool loopback = sde_mgmt->direction == SDE_EXAMPLE_DIR_LOOPBACK;
  ret = sde_hw_cfg_loopback_mode(&sde_mgmt->hw_ctrl, loopback);
  fail_on(ret, err, "failed to configure loopback mode");

  if (!loopback) {
    ret = sde_hw_cfg_atg_mode(&sde_mgmt->hw_ctrl, true, sde_mgmt->data_pattern, sde_mgmt->c2h_buffer.pkt_size);
    fail_on(ret, err, "failed to configure atg mode");
  }

err:
  return ret;
}

int sde_mgmt_cfg(int slot_id) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];

  ret = sde_mgmt_cfg_c2h(sde_mgmt);
  fail_on(ret, err, "failed to configure c2h");

  ret = sde_mgmt_cfg_h2c(sde_mgmt);
  fail_on(ret, err, "failed to configure h2c");

  ret = sde_mgmt_cfg_c2h_atg(sde_mgmt);
  fail_on(ret, err, "failed to configure c2h atg");

  ret = sde_mgmt_cfg_packets(sde_mgmt);
  fail_on(ret, err, "failed to configure packets");

err:
  return ret;
}

int sde_mgmt_wait_desc_credit(int slot_id, enum SDE_SUBSYSTEM subsystem, size_t num_desc) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);
  fail_on_with_code(num_desc > SDE_NUM_DESC, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "num_desc %ld is out of range", num_desc);

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];
  uint32_t* desc_consumed = (subsystem == SDE_SUBSYSTEM_C2H) ? &sde_mgmt->c2h_desc_consumed : &sde_mgmt->h2c_desc_consumed;

  size_t credits_available;
  int iters = 0;
  uint32_t desc_limit;
  do {
    if (subsystem == SDE_SUBSYSTEM_C2H) {
      desc_limit = sde_mgmt->c2h_status->desc_limit;
    } else if (subsystem == SDE_SUBSYSTEM_H2C) {
      desc_limit = sde_mgmt->h2c_status->desc_limit;
    }

    credits_available = desc_limit - *desc_consumed;

    iters++;
  } while ( credits_available < num_desc && iters < DESC_WAIT_MAX_ITERS);

  fail_on_with_code(credits_available < num_desc, err, ret, SDE_DESC_LIMIT_TIMEOUT,
    "Desc Credit Timeout credits_avail=%ld, num_desc=%ld, desc_limit=%d, desc_consumed=%d",
    credits_available, num_desc, desc_limit, *desc_consumed);

err:
  return ret;
}

int sde_mgmt_post_desc(int slot_id, enum SDE_SUBSYSTEM subsystem, size_t* num_desc) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);
  fail_on_with_code(num_desc == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "num_desc is NULL");
  fail_on_with_code(*num_desc > SDE_NUM_DESC, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "num_desc %ld is out of range", *num_desc);

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];
  uint32_t* desc_consumed = (subsystem == SDE_SUBSYSTEM_C2H) ? &sde_mgmt->c2h_desc_consumed : &sde_mgmt->h2c_desc_consumed;
  struct sde_dma_buffer* buffer = (subsystem == SDE_SUBSYSTEM_C2H) ? &sde_mgmt->c2h_buffer : &sde_mgmt->h2c_buffer;

  ret = sde_dma_post_desc(buffer, num_desc);

  *desc_consumed += *num_desc;

err:
  return ret;
}

int sde_mgmt_start_read(int slot_id, size_t size) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];

  if (size > 0) {
    // num_desc is the size / pkt_size rounded up (ceil), so add pkt_size - 1
    size_t num_desc = (size + sde_mgmt->c2h_buffer.pkt_size - 1) / sde_mgmt->c2h_buffer.pkt_size;
    ret = sde_mgmt_wait_desc_credit(slot_id, SDE_SUBSYSTEM_C2H, num_desc);
    fail_on(ret, err, "failed to wait desc credit");

    ret = sde_mgmt_post_desc(slot_id, SDE_SUBSYSTEM_C2H, &num_desc);
    fail_on(ret, err, "failed to post desc");
  }

err:
  return ret;
}

int sde_mgmt_read_md(int slot_id, struct sde_md* md) {
  int ret = 0;
  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);
  fail_on_with_code(md == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "md is NULL");

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];

  bool done = 0;
  size_t iters = 0;
  do {
    done = SDE_GET_BITFIELD(METADATA_STATUS_VALID, sde_mgmt->metadata[sde_mgmt->md_read_index].status);

    ++iters;
  } while(!done && iters < DESC_WAIT_MAX_ITERS);

  fail_on_with_code(done == 0, err, ret, SDE_METADATA_VALID_TIMEOUT, "Timeout waiting for valid metadata");

  uint32_t md_status = sde_mgmt->metadata[sde_mgmt->md_read_index].status;
  md->valid = SDE_GET_BITFIELD(METADATA_STATUS_VALID, md_status);
  md->eop   = SDE_GET_BITFIELD(METADATA_STATUS_EOP, md_status);
  md->length = sde_mgmt->metadata[sde_mgmt->md_read_index].length;

  sde_mgmt->metadata[sde_mgmt->md_read_index].status = 0x0;

  md->user_bits[0] = sde_mgmt->metadata[sde_mgmt->md_read_index].user & 0xffffffff;
  md->user_bits[1] = sde_mgmt->metadata[sde_mgmt->md_read_index].user >> 32;

  ++sde_mgmt->md_read_index;
  sde_mgmt->md_read_index &= (SDE_NUM_DESC - 1);

err:
  return ret;
}

int sde_mgmt_read_data(int slot_id, void *data, size_t size) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);
  fail_on_with_code(data == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "data is NULL");
  fail_on_with_code(size == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "size is 0");

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];
  struct sde_dma_buffer *buffer = &sde_mgmt->c2h_buffer;
  struct sde_md md;

  size_t data_read = 0;
  size_t iter = 0;
  size_t data_to_read = 0;
  while (data_read < size) {
    ret = sde_mgmt_read_md(slot_id, &md);
    fail_on(ret, err, "failed to read md");

    data_to_read = md.length < (size - data_read) ? md.length : (size - data_read);
    ret = sde_dma_read_data(buffer, data + data_read, data_to_read);
    fail_on(ret, err, "failed to read data");

    data_read += data_to_read;
    ++iter;
    log_info("read data %ld bytes, iter %ld", data_read, iter);
  }

err:
  return ret;
}

int sde_mgmt_prepare_write(int slot_id, void *data, size_t size) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);
  fail_on_with_code(data == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "data is NULL");
  fail_on_with_code(size == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "size is 0");

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];
  struct sde_dma_buffer *buffer = &sde_mgmt->h2c_buffer;

  size_t data_written = 0;
  size_t iter = 0;
  size_t data_to_write = 0;
  while (data_written < size) {
    data_to_write = buffer->pkt_size < (size - data_written) ? buffer->pkt_size : (size - data_written);
    ret = sde_dma_write_data(buffer, data + data_written, data_to_write);

    data_written += data_to_write;
    ++iter;
    log_info("write data %ld bytes, iter %ld", data_written, iter);
  }

err:
  return ret;
}

int sde_mgmt_write(int slot_id, size_t size) {
  int ret = 0;

  fail_on_with_code(slot_id >= SDE_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "slot_id %d is out of range", slot_id);
  fail_on_with_code(size == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "size is 0");

  struct sde_mgmt *sde_mgmt = &priv_sde_mgmt[slot_id];

  if (size > 0) {
    // num_desc is the size / pkt_size rounded up (ceil), so add pkt_size - 1
    size_t num_desc = (size + sde_mgmt->h2c_buffer.pkt_size - 1) / sde_mgmt->h2c_buffer.pkt_size;
    ret = sde_mgmt_wait_desc_credit(slot_id, SDE_SUBSYSTEM_H2C, num_desc);
    fail_on(ret, err, "failed to wait desc credit");

    ret = sde_mgmt_post_desc(slot_id, SDE_SUBSYSTEM_H2C, &num_desc);
    fail_on(ret, err, "failed to post desc");
  }

err:
  return ret;
}