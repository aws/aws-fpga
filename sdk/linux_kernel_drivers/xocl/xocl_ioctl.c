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

#include <linux/bitops.h>
#include <linux/swap.h>
#include <linux/dma-buf.h>
#include <linux/version.h>
#include <linux/eventfd.h>
#if LINUX_VERSION_CODE <= KERNEL_VERSION(3,0,0)
#include <drm/drm_backport.h>
#endif
#include <linux/string.h>
#include <drm/drmP.h>
#include "xocl_drv.h"
#include "xocl_ioctl.h"
#include "xocl_xdma.h"

static const struct axlf_section_header* get_axlf_section(const struct axlf* top, enum axlf_section_kind kind)
{
	int i = 0;
	printk(KERN_INFO "Trying to find section header for axlf section %d", kind);
	for(i = 0; i < top->m_header.m_numSections; i++)
	{
		printk(KERN_INFO "Section is %d",top->m_sections[i].m_sectionKind);
		if(top->m_sections[i].m_sectionKind == kind) {
			printk(KERN_INFO "Found section header for axlf");
			return &top->m_sections[i];
		}
	}
	printk(KERN_INFO "Did NOT find section header for axlf section %d", kind);
	return NULL;
}


static long xclbin_precheck_cleanup(struct drm_device *dev)
{
	struct drm_xocl_dev *xdev = dev->dev_private;
	struct drm_xocl_mem_topology *topology = &xdev->topology;
	long err = 0;
	short ddr = 0;
	unsigned i = 0;
	printk(KERN_INFO "%s XOCL: Existing bank count = %d\n", __FUNCTION__, topology->bank_count);
	ddr = 0;
	for (i= 0; i < topology->bank_count; i++) {
		if (topology->m_data[i].m_used) {
			ddr++;
			if (xdev->mm_usage_stat[ddr -1].bo_count !=0 ) {
				err = -EPERM;
				printk(KERN_INFO "%s The ddr %d has pre-existing buffer allocations, please exit and re-run.\n", __FUNCTION__, ddr -1);
			}
		}
	}

	printk(KERN_INFO "XOCL: Marker 4\n");
	//Cleanup the topology struct from the previous xclbin
	ddr = xocl_ddr_channel_count(dev);
	for (i = 0; i < ddr; i++) {
		if(topology->m_data[i].m_used) {
			printk(KERN_INFO "Taking down DDR : %d", ddr);
			drm_mm_takedown(&xdev->mm[i]);
		}
	}

	vfree(topology->m_data);
	vfree(topology->topology);
	memset(topology, 0, sizeof(struct drm_xocl_mem_topology));
	vfree(xdev->connectivity.connections);
	memset(&xdev->connectivity, 0, sizeof(xdev->connectivity));
	vfree(xdev->layout.layout);
	memset(&xdev->layout, 0, sizeof(xdev->layout));
	vfree(xdev->debug_layout.layout);
	memset(&xdev->debug_layout, 0, sizeof(xdev->debug_layout));

	return err;
}

int xocl_read_axlf_ioctl(struct drm_device *dev,
			void *data,
			struct drm_file *filp)
{
	struct drm_xocl_axlf *axlf_obj_ptr = data;
	struct drm_xocl_dev *xdev = dev->dev_private;
	long err = 0;
	unsigned i = 0;
	uint64_t copy_buffer_size = 0;
	struct axlf* copy_buffer = 0;
	const struct axlf_section_header *memHeader = 0;
	char __user *buffer =0;
	int32_t bank_count = 0;
	short ddr = 0;
	struct axlf bin_obj;
	struct drm_xocl_mem_topology *topology;

	printk(KERN_INFO "%s %s READ_AXLF IOCTL \n", DRV_NAME, __FUNCTION__);

	if(!xdev->unified) {
		printk(KERN_INFO "XOCL: not unified dsa");
		return err;
	}

	printk(KERN_INFO "XOCL: Marker 0 %p\n", data);
	if (copy_from_user((void *)&bin_obj, (void*)axlf_obj_ptr->xclbin, sizeof(struct axlf)))
		return -EFAULT;
	if (memcmp(bin_obj.m_magic, "xclbin2", 8))
		return -EINVAL;
	//Ignore timestamp matching for AWS platform
	if(bin_obj.m_header.m_featureRomTimeStamp != xdev->header.TimeSinceEpoch && strstr(xdev->header.VBNVName, "xilinx_aw") == NULL) {
		printk(KERN_ERR "TimeStamp of ROM did not match Xclbin\n");
		return -EINVAL;
	}

	printk(KERN_INFO "XOCL: VBNV and TimeStamps matched\n");

	if(bin_obj.m_uniqueId == xdev->unique_id_last_bitstream) {
		printk(KERN_INFO "Skipping repopulating topology, connectivity,ip_layout data\n");
		return err;
	}

	//Switching the xclbin, make sure none of the buffers are used.
        err = xclbin_precheck_cleanup(dev);
	if(err)
		return err;

	//Copy from user space and proceed.
	copy_buffer_size = (bin_obj.m_header.m_numSections)*sizeof(struct axlf_section_header) + sizeof(struct axlf);
	copy_buffer = (struct axlf*)vmalloc(copy_buffer_size);
	if(!copy_buffer) {
		printk(KERN_ERR "Unable to create copy_buffer");
		return -EFAULT;
	}
	printk(KERN_INFO "XOCL: Marker 5\n");

	if (copy_from_user((void *)copy_buffer, (void *)axlf_obj_ptr->xclbin, copy_buffer_size)) {
		err = -EFAULT;
		goto done;
	}

	buffer = (char __user *)axlf_obj_ptr->xclbin;
	err = !access_ok(VERIFY_READ, buffer, bin_obj.m_header.m_length);
	if (err) {
		err = -EFAULT;
		goto done;
	}

	//----
	printk(KERN_INFO "Finding IP_LAYOUT section\n");
	memHeader = get_axlf_section(copy_buffer, IP_LAYOUT);
	if (memHeader == 0) {
		printk(KERN_INFO "Did not find IP_LAYOUT section.\n");
	} else {
		printk(KERN_INFO "%s XOCL: IP_LAYOUT offset = %llx, size = %llx, xclbin length = %llx\n", __FUNCTION__, memHeader->m_sectionOffset , memHeader->m_sectionSize, bin_obj.m_header.m_length);

		if((memHeader->m_sectionOffset + memHeader->m_sectionSize) > bin_obj.m_header.m_length) {
			printk(KERN_INFO "%s XOCL: IP_LAYOUT section extends beyond xclbin boundary %llx\n", __FUNCTION__, bin_obj.m_header.m_length);
			err = -EINVAL;
			goto done;
		}
		printk(KERN_INFO "XOCL: Marker 5.1\n");
		buffer += memHeader->m_sectionOffset;
		xdev->layout.layout = vmalloc(memHeader->m_sectionSize);
		err = copy_from_user(xdev->layout.layout, buffer, memHeader->m_sectionSize);
		printk(KERN_INFO "XOCL: Marker 5.2\n");
		if (err)
			goto done;
		xdev->layout.size = memHeader->m_sectionSize;
		printk(KERN_INFO "XOCL: Marker 5.3\n");
	}

	//----
	printk(KERN_INFO "Finding DEBUG_IP_LAYOUT section\n");
	memHeader = get_axlf_section(copy_buffer, DEBUG_IP_LAYOUT);
	if (memHeader == 0) {
		printk(KERN_INFO "Did not find DEBUG_IP_LAYOUT section.\n");
	} else {
		printk(KERN_INFO "%s XOCL: DEBUG_IP_LAYOUT offset = %llx, size = %llx, xclbin length = %llx\n", __FUNCTION__, memHeader->m_sectionOffset , memHeader->m_sectionSize, bin_obj.m_header.m_length);

		if((memHeader->m_sectionOffset + memHeader->m_sectionSize) > bin_obj.m_header.m_length) {
			printk(KERN_INFO "%s XOCL: DEBUG_IP_LAYOUT section extends beyond xclbin boundary %llx\n", __FUNCTION__, bin_obj.m_header.m_length);
			err = -EINVAL;
			goto done;
		}
		printk(KERN_INFO "XOCL: Marker 6.1\n");
		buffer = (char __user *)axlf_obj_ptr->xclbin;
		buffer += memHeader->m_sectionOffset;
		xdev->debug_layout.layout = vmalloc(memHeader->m_sectionSize);
		err = copy_from_user(xdev->debug_layout.layout, buffer, memHeader->m_sectionSize);
		printk(KERN_INFO "XOCL: Marker 6.2\n");
		if (err)
			goto done;
		xdev->debug_layout.size = memHeader->m_sectionSize;
		printk(KERN_INFO "XOCL: Marker 6.3\n");
	}

	//---
	printk(KERN_INFO "Finding CONNECTIVITY section\n");
	memHeader = get_axlf_section(copy_buffer, CONNECTIVITY);
	if (memHeader == 0) {
		printk(KERN_INFO "Did not find CONNECTIVITY section.\n");
	} else {
		printk(KERN_INFO "%s XOCL: CONNECTIVITY offset = %llx, size = %llx\n", __FUNCTION__, memHeader->m_sectionOffset , memHeader->m_sectionSize);
		if((memHeader->m_sectionOffset + memHeader->m_sectionSize) > bin_obj.m_header.m_length) {
			err = -EINVAL;
			goto done;
		}
		buffer = (char __user *)axlf_obj_ptr->xclbin;
		buffer += memHeader->m_sectionOffset;
		xdev->connectivity.connections = vmalloc(memHeader->m_sectionSize);
		err = copy_from_user(xdev->connectivity.connections, buffer, memHeader->m_sectionSize);
		if (err)
			goto done;
		xdev->connectivity.size = memHeader->m_sectionSize;
	}

	//---
	printk(KERN_INFO "Finding MEM_TOPOLOGY section\n");
	memHeader = get_axlf_section(copy_buffer, MEM_TOPOLOGY);
	if (memHeader == 0) {
		printk(KERN_INFO "Did not find MEM_TOPOLOGY section.\n");
		err = -EINVAL;
		goto done;
	}
	printk(KERN_INFO "XOCL: Marker 7\n");

	printk(KERN_INFO "%s XOCL: MEM_TOPOLOGY offset = %llx, size = %llx\n", __FUNCTION__, memHeader->m_sectionOffset , memHeader->m_sectionSize);

	if((memHeader->m_sectionOffset + memHeader->m_sectionSize) > bin_obj.m_header.m_length) {
		err = -EINVAL;
		goto done;
	}


	printk(KERN_INFO "XOCL: Marker 8\n");

	buffer = (char __user *)axlf_obj_ptr->xclbin;
	buffer += memHeader->m_sectionOffset;

	xdev->topology.topology = vmalloc(memHeader->m_sectionSize);
	err = copy_from_user(xdev->topology.topology, buffer, memHeader->m_sectionSize);
	if (err)
	    goto done;
	xdev->topology.size = memHeader->m_sectionSize;

	get_user(bank_count, buffer);
	xdev->topology.bank_count = bank_count;
	buffer += offsetof(struct mem_topology, m_mem_data);
	xdev->topology.m_data_length = bank_count*sizeof(struct mem_data);
	xdev->topology.m_data = vmalloc(xdev->topology.m_data_length);
	err = copy_from_user(xdev->topology.m_data, buffer, bank_count*sizeof(struct mem_data));
	if (err) {
		err = -EFAULT;
		goto done;
	}


	printk(KERN_INFO "XOCL: Marker 9\n");

	topology = &xdev->topology;

	printk(KERN_INFO "XOCL: Topology Bank count = %d, data_length = %d\n", topology->bank_count, xdev->topology.m_data_length);

	xdev->mm = devm_kzalloc(dev->dev, sizeof(struct drm_mm) * topology->bank_count, GFP_KERNEL);
	xdev->mm_usage_stat = devm_kzalloc(dev->dev, sizeof(struct drm_xocl_mm_stat) * topology->bank_count, GFP_KERNEL);
	if (!xdev->mm || !xdev->mm_usage_stat) {
		err = -ENOMEM;
		goto done;
	}

	//Check if sizes are same across banks.
	ddr = 0;
	for (i=0; i < topology->bank_count; i++)
	{
    	        printk(KERN_INFO "XOCL, DDR Info Index: %d Type:%d Used:%d Size:%llx Base_addr:%llx\n", i,
			topology->m_data[i].m_type, topology->m_data[i].m_used, topology->m_data[i].m_size,
			topology->m_data[i].m_base_address);
		if (topology->m_data[i].m_used)
		{
			ddr++;
			if ((topology->bank_size !=0) && (topology->bank_size != topology->m_data[i].m_size)) {
				//we support only same sized banks for initial testing, so return error.
				printk(KERN_INFO "%s err: %ld\n", __FUNCTION__, err);
				err = -EFAULT;
				vfree(xdev->topology.m_data);
				memset(&xdev->topology, 0, sizeof(xdev->topology));
				goto done;
			}
			topology->bank_size = topology->m_data[i].m_size;
		}
	}

	//xdev->topology.used_bank_count = ddr;
	printk(KERN_INFO "XOCL: Unified flow, used bank count :%d bank size(KB):%llx\n", ddr, xdev->topology.bank_size);

	//initialize the used banks and their sizes. Currently only fixed sizes are supported.
	for (i=0; i < topology->bank_count; i++)
	{
		if (topology->m_data[i].m_used) {
			printk(KERN_INFO "%s Allocating DDR:%d with base_addr:%llx, size %llx \n", __FUNCTION__, i,
				topology->m_data[i].m_base_address, topology->m_data[i].m_size*1024);
			drm_mm_init(&xdev->mm[i], topology->m_data[i].m_base_address, topology->m_data[i].m_size*1024);
			printk(KERN_INFO "drm_mm_init called \n");
		}
	}

	//Populate with "this" bitstream, so avoid redownload the next time
	xdev->unique_id_last_bitstream = bin_obj.m_uniqueId;

done:
	printk(KERN_INFO "%s err: %ld\n", __FUNCTION__, err);
	vfree(copy_buffer);
	return err;

}

int xocl_ctx_ioctl(struct drm_device *dev, void *data,
		   struct drm_file *filp)
{
	unsigned long flags;
	int ret = 0;
	struct drm_xocl_dev *xdev = dev->dev_private;
	struct drm_xocl_ctx *args = data;

	if (args->op == XOCL_CTX_OP_FREE_CTX) {
		DRM_INFO("Releasing context for pid %d\n", pid_nr(task_tgid(current)));
		spin_lock_irqsave(&xdev->exec.ctx_list_lock, flags);
		spin_unlock_irqrestore(&xdev->exec.ctx_list_lock, flags);
		return 0;
	}

	if (args->op != XOCL_CTX_OP_ALLOC_CTX)
		return -EINVAL;

	DRM_INFO("Creating context for pid %d\n", pid_nr(task_tgid(current)));

	spin_lock_irqsave(&xdev->exec.ctx_list_lock, flags);

	spin_unlock_irqrestore(&xdev->exec.ctx_list_lock, flags);
	return ret;
}


int xocl_debug_ioctl(struct drm_device *dev,
		     void *data,
		     struct drm_file *filp)
{
	int ret = -EINVAL;
	//struct drm_xocl_debug *args = data;
	return ret;
}



int xocl_user_intr_ioctl(struct drm_device *dev, void *data,
			 struct drm_file *filp)

{
	struct eventfd_ctx *trigger;
	int ret = 0;
	struct drm_xocl_user_intr *args = data;
	struct drm_xocl_dev *xdev = dev->dev_private;
	struct drm_xocl_client_ctx *fpriv = filp->driver_priv;

	if ((args->msix >= XOCL_USER_INTR_END) || (args->msix < XOCL_USER_INTR_START))
		return -EINVAL;
	mutex_lock(&xdev->exec.user_msix_table_lock);
	if (xdev->exec.user_msix_table[args->msix]) {
		ret = -EPERM;
		goto out;
	}

	if (args->fd < 0)
		goto out;
	trigger = eventfd_ctx_fdget(args->fd);
	if (IS_ERR(trigger)) {
		ret = PTR_ERR(trigger);
		goto out;
	}
	xdev->exec.user_msix_table[args->msix] = trigger;
	xdma_user_interrupt_config(xdev, args->msix, true);
	fpriv->eventfd_bitmap |= (1 << args->msix);
out:
	mutex_unlock(&xdev->exec.user_msix_table_lock);
	return ret;
}
