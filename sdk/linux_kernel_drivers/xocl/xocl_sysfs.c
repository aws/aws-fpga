/*
 * Copyright (C) 2016-2018 Xilinx, Inc
 *
 * Authors:
 *    Umang Parekh <umang.parekh@xilinx.com>
 *
 * sysfs for the device attributes.
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

#include "xocl_drv.h"

//-xclbinid--
static ssize_t xclbinid_show(struct device *dev,
    struct device_attribute *attr, char *buf)
{
	struct drm_device *ddev = dev_get_drvdata(dev);
	struct drm_xocl_dev *xdev = ddev->dev_private;
	return sprintf(buf, "%llx\n", xdev->unique_id_last_bitstream);
}

static DEVICE_ATTR_RO(xclbinid);

//-Base address--
static ssize_t dr_base_addr_show(struct device *dev,
    struct device_attribute *attr, char *buf)
{
	struct drm_device *ddev = dev_get_drvdata(dev);
	struct drm_xocl_dev *xdev = ddev->dev_private;

	//TODO: Fix: DRBaseAddress no longer required in feature rom
	if(xdev->header.MajorVersion >= 10)
		return sprintf(buf, "%llu\n", xdev->header.DRBaseAddress);
	else
		return sprintf(buf, "%u\n", 0);
}

static DEVICE_ATTR_RO(dr_base_addr);


//-Mem_topology--
static ssize_t mem_topology_show(struct device *dev,
    struct device_attribute *attr, char *buf)
{
	printk(KERN_INFO "%s %s In mem_topology_show function \n", DRV_NAME, __FUNCTION__);
	struct drm_device *ddev = dev_get_drvdata(dev);
	struct drm_xocl_dev *xdev = ddev->dev_private;
	memcpy(buf, xdev->topology.topology, xdev->topology.size);
	printk(KERN_INFO "%s %s Mem-copied %llx bytes \n", DRV_NAME, __FUNCTION__, xdev->topology.size);
	return xdev->topology.size;
}

static DEVICE_ATTR_RO(mem_topology);

//-Connectivity--
static ssize_t connectivity_show(struct device *dev,
    struct device_attribute *attr, char *buf)
{
	printk(KERN_INFO "%s %s In connectivity_show function \n", DRV_NAME, __FUNCTION__);
	struct drm_device *ddev = dev_get_drvdata(dev);
	struct drm_xocl_dev *xdev = ddev->dev_private;
	memcpy(buf, xdev->connectivity.connections, xdev->connectivity.size);
	return xdev->connectivity.size;
}

static DEVICE_ATTR_RO(connectivity);

//-IP_layout--
static ssize_t ip_layout_show(struct device *dev,
    struct device_attribute *attr, char *buf)
{
	printk(KERN_INFO "%s %s In ip_layout_show function \n", DRV_NAME, __FUNCTION__);
	struct drm_device *ddev = dev_get_drvdata(dev);
	struct drm_xocl_dev *xdev = ddev->dev_private;
	memcpy(buf, xdev->layout.layout, xdev->layout.size);
	return xdev->layout.size;
}

static DEVICE_ATTR_RO(ip_layout);

//- Debug IP_layout--
static ssize_t debug_ip_layout_show(struct device *dev,
    struct device_attribute *attr, char *buf)
{
	printk(KERN_INFO "%s %s In debug_ip_layout_show function \n", DRV_NAME, __FUNCTION__);
	struct drm_device *ddev = dev_get_drvdata(dev);
	struct drm_xocl_dev *xdev = ddev->dev_private;
	memcpy(buf, xdev->debug_layout.layout, xdev->debug_layout.size);
	printk(KERN_INFO "%s %s Mem-copied %llx bytes \n", DRV_NAME, __FUNCTION__, xdev->debug_layout.size);
	return xdev->debug_layout.size;
}

static DEVICE_ATTR_RO(debug_ip_layout);


//---
int xocl_init_sysfs(struct device *dev)
{
	int result = device_create_file(dev, &dev_attr_xclbinid);
	if(result)
		return result;
	result = device_create_file(dev, &dev_attr_dr_base_addr);
	if(result)
		return result;
	result = device_create_file(dev, &dev_attr_connectivity);
	if(result)
		return result;
	result = device_create_file(dev, &dev_attr_ip_layout);
	if(result)
		return result;
	result = device_create_file(dev, &dev_attr_debug_ip_layout);
	if(result)
		return result;
	result = device_create_file(dev, &dev_attr_mem_topology);
	return result;
}

void xocl_fini_sysfs(struct device *dev)
{
	printk(KERN_INFO "%s %s Cleaning up sys files \n", DRV_NAME, __FUNCTION__);
	device_remove_file(dev, &dev_attr_xclbinid);
	device_remove_file(dev, &dev_attr_dr_base_addr);
	device_remove_file(dev, &dev_attr_mem_topology);
	device_remove_file(dev, &dev_attr_connectivity);
	device_remove_file(dev, &dev_attr_ip_layout);
	device_remove_file(dev, &dev_attr_debug_ip_layout);
}
