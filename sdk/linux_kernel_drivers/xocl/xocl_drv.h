/*
 * Copyright (C) 2016-2018 Xilinx, Inc
 *
 * Authors:
 *    Sonal Santan <sonal.santan@xilinx.com>
 *
 * A GEM style device manager for PCIe based OpenCL accelerators.
 *
 * This software is licensed under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation, and
 * may be copied, distributed, and modified under those terms.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

#ifndef _XCL_XOCL_DRV_H_
#define _XCL_XOCL_DRV_H_

#include <linux/version.h>
#if LINUX_VERSION_CODE <= KERNEL_VERSION(3,0,0)
#include <drm/drm_backport.h>
#endif
#include <drm/drmP.h>
#include <drm/drm_gem.h>
#include <drm/drm_mm.h>
#include <linux/semaphore.h>
#include <linux/init_task.h>
#include <linux/list.h>
#include <linux/wait.h>
#include "xclfeatures.h"
#include "xclbin2.h" // originally xclbin.h
#include "xocl_ioctl.h"
#include "xocl_exec.h"
#include "xocl_xvc.h"
#include "libxdma.h"

#define DRV_NAME "xocl"

// For CMA kernel command line should be cma=nn[MG]@[start[MG]

#define XOCL_BO_USERPTR (1 << 31)
#define XOCL_BO_IMPORT  (1 << 30)
#define XOCL_BO_EXECBUF (1 << 29)
#define XOCL_BO_CMA     (1 << 28)
#define XOCL_BO_DDR0 (1 << 0)
#define XOCL_BO_DDR1 (1 << 1)
#define XOCL_BO_DDR2 (1 << 2)
#define XOCL_BO_DDR3 (1 << 3)
#define XOCL_BO_ARE  (1 << 4) //When the BO is imported from an ARE device. This is remote BO to be accessed over ARE

#define XOCL_CHANNEL_COUNT 	4
#define XOCL_RD_MTX  		0
#define XOCL_WR_MTX  		1

#define XOCL_CMA_BASE 0x200000000 // (8 GB)
#define XOCL_CMA_SIZE 0x020000000 // (512 MB)
#define XOCL_CMA_NAME "PCISlave"

#define XOCL_ARE_HOP 0x400000000ull

#define XOCL_FEATURE_ROM     0x0B0000
#define XOCL_SCHD_HW         0x180000
#define XOCL_SCHD_CMD_QUEUE  0x190000
#define XOCL_SCHD_CMD_STATUS 0x190000

struct cma;

struct drm_xocl_exec_metadata {
	enum drm_xocl_execbuf_state state;
	unsigned int                index;
};

struct drm_xocl_bo {
	/* drm base object */
	struct drm_gem_object base;
	struct drm_mm_node   *mm_node;
	struct drm_xocl_exec_metadata metadata;
	struct page         **pages;
	struct sg_table      *sgt;
	void                 *vmapping;
	unsigned              flags;
};

struct drm_xocl_unmgd {
	struct page         **pages;
	struct sg_table      *sgt;
	unsigned int          npages;
	unsigned              flags;
};

struct drm_xocl_mem_topology {
	//TODO : check the first 4 entries - remove unneccessary ones.
	int32_t             bank_count;
	struct mem_data*    m_data;
	u32                 m_data_length; //length of the mem_data section.
	uint64_t            bank_size; //in KB. Currently only fixed sizes are supported.
	uint64_t	    size;
	struct mem_topology *topology;
};

struct drm_xocl_connectivity {
	uint64_t            size;
	struct connectivity *connections;
};

struct drm_xocl_layout {
	uint64_t            size;
	struct ip_layout    *layout;
};

struct drm_xocl_debug_layout {
	uint64_t            size;
	struct debug_ip_layout    *layout;
};

struct drm_xocl_dev {
	struct drm_device       *ddev;
	/* The feature Rom header */
	struct FeatureRomHeader  header;
	/* Number of bidirectional channels */
	unsigned                 channel;
	/* Memory manager array, one per DDR channel */
	struct drm_mm           *mm;
	/* Memory manager lock */
	struct mutex             mm_lock;
	/* Semaphore, one for each direction */
	struct semaphore         channel_sem[2];
	/* Channel usage bitmasks, one for each direction
	 * bit 1 indicates channel is free, bit 0 indicates channel is free
	 */
	volatile unsigned long   channel_bitmap[2];
	unsigned long long      *channel_usage[2];
	struct drm_xocl_mm_stat *mm_usage_stat;
	struct xdma_dev         *xdma_handle;
	struct cma              *cma_blk;
	bool                     offline;
	/* Lock for stats */
	struct mutex             stat_lock;
	void *__iomem            user_bar;
	phys_addr_t              res_start;
	resource_size_t          res_len;
	bool                     unified; //unified platform, populated from FeatureROM,
	u64                      unique_id_last_bitstream;
	struct xocl_xvc                xvc;
	struct drm_xocl_exec_core      exec;
	struct drm_xocl_mem_topology   topology;
	struct drm_xocl_layout         layout;
	struct drm_xocl_debug_layout   debug_layout;
	struct drm_xocl_connectivity   connectivity;
};

static inline struct drm_gem_object *xocl_gem_object_lookup(struct drm_device *dev,
							    struct drm_file *filp,
							    u32 handle)
{
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,7,0)
	return drm_gem_object_lookup(filp, handle);
#elif defined(RHEL_RELEASE_CODE)
#if RHEL_RELEASE_CODE >= RHEL_RELEASE_VERSION(7,4)
	return drm_gem_object_lookup(filp, handle);
#else
	return drm_gem_object_lookup(dev, filp, handle);
#endif
#else
	return drm_gem_object_lookup(dev, filp, handle);
#endif
}

static inline struct drm_xocl_bo *to_xocl_bo(struct drm_gem_object *bo)
{
	return (struct drm_xocl_bo *)bo;
}

static inline struct drm_xocl_dev *bo_xocl_dev(const struct drm_xocl_bo *bo)
{
	return bo->base.dev->dev_private;
}

static inline unsigned xocl_bo_ddr_idx(unsigned flags)
{
	const unsigned ddr = flags & 0xf;
	if (!ddr)
		return 0xffffffff;
	return __builtin_ctz(ddr);
}

static inline unsigned short xocl_ddr_channel_count(const struct drm_device *drm)
{
	struct drm_xocl_dev *xdev = drm->dev_private;
	struct drm_xocl_mem_topology *topology;
	if(!xdev->unified)
		return xdev->header.DDRChannelCount;
	topology = &xdev->topology;
	return topology->bank_count;
}

static inline unsigned long long xocl_ddr_channel_size(const struct drm_device *drm)
{
	struct drm_xocl_dev *xdev = drm->dev_private;
	struct drm_xocl_mem_topology *topology;

	if(!xdev->unified) {
		/* Channel size is in GB */
		return xdev->header.DDRChannelSize * 0x40000000ull;
	}
	topology = &xdev->topology;
	return topology->bank_size;
}

static inline bool xocl_bo_userptr(const struct drm_xocl_bo *bo)
{
	return (bo->flags & XOCL_BO_USERPTR);
}

static inline bool xocl_bo_import(const struct drm_xocl_bo *bo)
{
	return (bo->flags & XOCL_BO_IMPORT);
}

static inline bool xocl_bo_execbuf(const struct drm_xocl_bo *bo)
{
	return (bo->flags & XOCL_BO_EXECBUF);
}

static inline bool xocl_bo_cma(const struct drm_xocl_bo *bo)
{
	return (bo->flags & XOCL_BO_CMA);
}

int xocl_create_bo_ioctl(struct drm_device *dev, void *data,
			 struct drm_file *filp);
int xocl_userptr_bo_ioctl(struct drm_device *dev,
			  void *data,
			  struct drm_file *filp);
int xocl_sync_bo_ioctl(struct drm_device *dev, void *data,
		       struct drm_file *filp);
int xocl_map_bo_ioctl(struct drm_device *dev, void *data,
		      struct drm_file *filp);
int xocl_info_bo_ioctl(struct drm_device *dev, void *data,
		       struct drm_file *filp);
int xocl_pwrite_bo_ioctl(struct drm_device *dev, void *data,
			 struct drm_file *filp);
int xocl_pread_bo_ioctl(struct drm_device *dev, void *data,
			struct drm_file *filp);
int xocl_ctx_ioctl(struct drm_device *dev, void *data,
		   struct drm_file *filp);
int xocl_pwrite_unmgd_ioctl(struct drm_device *dev, void *data,
			    struct drm_file *filp);
int xocl_pread_unmgd_ioctl(struct drm_device *dev, void *data,
			   struct drm_file *filp);
int xocl_usage_stat_ioctl(struct drm_device *dev, void *data,
			   struct drm_file *filp);
int xocl_read_axlf_ioctl(struct drm_device *dev, void *data,
			   struct drm_file *filp);


void xocl_describe(const struct drm_xocl_bo *obj);

void xocl_free_bo(struct drm_gem_object *obj);

int xocl_migrate_bo(struct drm_device *ddev, const struct drm_xocl_bo *xobj,
		    enum drm_xocl_sync_bo_dir dir);

int xocl_user_event(int irq, struct drm_xocl_dev *xdev);

/**
 * DMA-BUF support
 */
struct drm_gem_object *xocl_gem_prime_import_sg_table(struct drm_device *dev,
						      struct dma_buf_attachment *attach, struct sg_table *sgt);

struct sg_table *xocl_gem_prime_get_sg_table(struct drm_gem_object *obj);

void *xocl_gem_prime_vmap(struct drm_gem_object *obj);

void xocl_gem_prime_vunmap(struct drm_gem_object *obj, void *vaddr);

/**
 * Sysfs related functions
 */
int xocl_init_sysfs(struct device *dev);
void xocl_fini_sysfs(struct device *dev);

/**
 * DEBUG and EXEC support
 */

int xocl_debug_ioctl(struct drm_device *dev, void *data,
		     struct drm_file *filp);
int xocl_execbuf_ioctl(struct drm_device *dev, void *data,
		       struct drm_file *filp);

int xocl_user_intr_ioctl(struct drm_device *dev, void *data,
			 struct drm_file *filp);

#endif

// 67d7842dbbe25473c3c32b93c0da8047785f30d78e8a024de1b57352245f9689
