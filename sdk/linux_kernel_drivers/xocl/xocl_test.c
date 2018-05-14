/**
 *  Copyright (C) 2018 Xilinx, Inc
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 * 
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

#include <linux/kthread.h>
#include "xocl_drv.h"

int xocl_test_interval = 5;
bool xocl_test_on = true;

/**
 * TODO:
 * Test drm_send_event() with event object initialized with drm_event_reserve_init()
 * to send events for CUs
 */
static int xocl_test_thread_main(void *data)
{
#if 0
	struct timeval now;
	struct drm_xocl_dev *xdev = (struct drm_xocl_dev *)data;
	int irq = 0;
	int count = 0;
	while (!kthread_should_stop()) {
		ssleep(xocl_test_interval);
		do_gettimeofday(&now);
		DRM_INFO("irq[%d] tv_sec[%ld]tv_usec[%ld]\n", irq, now.tv_sec, now.tv_usec);
		xocl_user_event(irq, xdev);
		irq++;
		irq &= 0xf;
		count++;
	}
	printk(KERN_INFO "The xocl test thread has terminated.");
#endif
	return 0;
}

int xocl_init_test_thread(struct drm_xocl_dev *xdev)
{
	int ret = 0;
#if 0
	xdev->exec.test_kthread = kthread_run(xocl_test_thread_main, (void *)xdev, "xocl-test-thread");
	DRM_DEBUG(__func__);
	if (IS_ERR(xdev->exec.test_kthread)) {
		DRM_ERROR(__func__);
		ret = PTR_ERR(xdev->exec.test_kthread);
		xdev->exec.test_kthread = NULL;
	}
#endif
	return ret;
}

int xocl_fini_test_thread(struct drm_xocl_dev *xdev)
{
	int ret = 0;
#if 0
	if (!xdev->exec.test_kthread)
		return 0;
	ret = kthread_stop(xdev->exec.test_kthread);
	ssleep(xocl_test_interval);
	xdev->exec.test_kthread = NULL;
	DRM_DEBUG(__func__);
#endif
	return ret;
}
