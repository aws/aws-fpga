/*******************************************************************************
 *
 * Xilinx XDMA IP Core Linux Driver
 * Copyright(c) 2015 - 2020 Xilinx, Inc.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms and conditions of the GNU General Public License,
 * version 2, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * The full GNU General Public License is included in this distribution in
 * the file called "LICENSE".
 *
 * Karen Xie <karen.xie@xilinx.com>
 *
 ******************************************************************************/

#define pr_fmt(fmt)	KBUILD_MODNAME ":%s: " fmt, __func__

#include "xdma_thread.h"

#include <linux/kernel.h>
#include <linux/slab.h>


/* ********************* global variables *********************************** */
static struct xdma_kthread *cs_threads;
static unsigned int thread_cnt;


/* ********************* static function definitions ************************ */
static int xdma_thread_cmpl_status_pend(struct list_head *work_item)
{
	struct xdma_engine *engine = list_entry(work_item, struct xdma_engine,
						cmplthp_list);
	int pend = 0;
	unsigned long flags;

	spin_lock_irqsave(&engine->lock, flags);
		pend = !list_empty(&engine->transfer_list);
	spin_unlock_irqrestore(&engine->lock, flags);

	return pend;
}

static int xdma_thread_cmpl_status_proc(struct list_head *work_item)
{
	struct xdma_engine *engine;
	struct xdma_transfer * transfer;

	engine = list_entry(work_item, struct xdma_engine, cmplthp_list);
	transfer = list_entry(engine->transfer_list.next, struct xdma_transfer,
			entry);
	engine_service_poll(engine, transfer->desc_num);
	return 0;
}



static inline int xthread_work_pending(struct xdma_kthread *thp)
{
	struct list_head *work_item, *next;

	/* any work items assigned to this thread? */
	if (list_empty(&thp->work_list))
		return 0;


	/* any work item has pending work to do? */
	list_for_each_safe(work_item, next, &thp->work_list) {
		if (thp->fpending && thp->fpending(work_item))
			return 1;

	}
	return 0;
}

static inline void xthread_reschedule(struct xdma_kthread *thp)
{
	if (thp->timeout) {
		pr_debug_thread("%s rescheduling for %u seconds",
				thp->name, thp->timeout);
		wait_event_interruptible_timeout(thp->waitq, thp->schedule,
					      msecs_to_jiffies(thp->timeout));
	} else {
		pr_debug_thread("%s rescheduling", thp->name);
		wait_event_interruptible(thp->waitq, thp->schedule);
	}
}

static int xthread_main(void *data)
{
	struct xdma_kthread *thp = (struct xdma_kthread *)data;

	pr_debug_thread("%s UP.\n", thp->name);

	disallow_signal(SIGPIPE);

	if (thp->finit)
		thp->finit(thp);


	while (!kthread_should_stop()) {

		struct list_head *work_item, *next;

		pr_debug_thread("%s interruptible\n", thp->name);

		/* any work to do? */
		lock_thread(thp);
		if (!xthread_work_pending(thp)) {
			unlock_thread(thp);
			xthread_reschedule(thp);
			lock_thread(thp);
		}
		thp->schedule = 0;

		if (thp->work_cnt) {
			pr_debug_thread("%s processing %u work items\n",
					thp->name, thp->work_cnt);
			/* do work */
			list_for_each_safe(work_item, next, &thp->work_list) {
				thp->fproc(work_item);
			}
		}
		unlock_thread(thp);
		schedule();
	}

	pr_debug_thread("%s, work done.\n", thp->name);

	if (thp->fdone)
		thp->fdone(thp);

	pr_debug_thread("%s, exit.\n", thp->name);
	return 0;
}


int xdma_kthread_start(struct xdma_kthread *thp, char *name, int id)
{
	int len;
	int node;

	if (thp->task) {
		pr_warn("kthread %s task already running?\n", thp->name);
		return -EINVAL;
	}

	len = snprintf(thp->name, sizeof(thp->name), "%s%d", name, id);
	if (len < 0)
		return -EINVAL;

	thp->id = id;

	spin_lock_init(&thp->lock);
	INIT_LIST_HEAD(&thp->work_list);
	init_waitqueue_head(&thp->waitq);

	node = cpu_to_node(thp->cpu);
	pr_debug("node : %d\n", node);

	thp->task = kthread_create_on_node(xthread_main, (void *)thp,
					node, "%s", thp->name);
	if (IS_ERR(thp->task)) {
		pr_err("kthread %s, create task failed: 0x%lx\n",
			thp->name, (unsigned long)IS_ERR(thp->task));
		thp->task = NULL;
		return -EFAULT;
	}

	kthread_bind(thp->task, thp->cpu);

	pr_debug_thread("kthread 0x%p, %s, cpu %u, task 0x%p.\n",
		thp, thp->name, thp->cpu, thp->task);

	wake_up_process(thp->task);
	return 0;
}


int xdma_kthread_stop(struct xdma_kthread *thp)
{
	int rv;

	if (!thp->task) {
		pr_debug_thread("kthread %s, already stopped.\n", thp->name);
		return 0;
	}

	thp->schedule = 1;
	rv = kthread_stop(thp->task);
	if (rv < 0) {
		pr_warn("kthread %s, stop err %d.\n", thp->name, rv);
		return rv;
	}

	pr_debug_thread("kthread %s, 0x%p, stopped.\n", thp->name, thp->task);
	thp->task = NULL;

	return 0;
}



void xdma_thread_remove_work(struct xdma_engine *engine)
{
	struct xdma_kthread *cmpl_thread;
	unsigned long flags;

	spin_lock_irqsave(&engine->lock, flags);
	cmpl_thread = engine->cmplthp;
	engine->cmplthp = NULL;

//	pr_debug("%s removing from thread %s, %u.\n",
//		descq->conf.name, cmpl_thread ? cmpl_thread->name : "?",
//		cpu_idx);

	spin_unlock_irqrestore(&engine->lock, flags);

#if 0
	if (cpu_idx < cpu_count) {
		spin_lock(&qcnt_lock);
		per_cpu_qcnt[cpu_idx]--;
		spin_unlock(&qcnt_lock);
	}
#endif

	if (cmpl_thread) {
		lock_thread(cmpl_thread);
		list_del(&engine->cmplthp_list);
		cmpl_thread->work_cnt--;
		unlock_thread(cmpl_thread);
	}
}

void xdma_thread_add_work(struct xdma_engine *engine)
{
	struct xdma_kthread *thp = cs_threads;
	unsigned int v = 0;
	int i, idx = thread_cnt;
	unsigned long flags;

	/* Polled mode only */
	for (i = 0; i < thread_cnt; i++, thp++) {
		lock_thread(thp);
		if (idx == thread_cnt) {
			v = thp->work_cnt;
			idx = i;
		} else if (!thp->work_cnt) {
			idx = i;
			unlock_thread(thp);
			break;
		} else if (thp->work_cnt < v)
			idx = i;
		unlock_thread(thp);
	}

	thp = cs_threads + idx;
	lock_thread(thp);
	list_add_tail(&engine->cmplthp_list, &thp->work_list);
	engine->intr_work_cpu = idx;
	thp->work_cnt++;
	unlock_thread(thp);

	pr_info("%s 0x%p assigned to cmpl status thread %s,%u.\n",
		engine->name, engine, thp->name, thp->work_cnt);


	spin_lock_irqsave(&engine->lock, flags);
	engine->cmplthp = thp;
	spin_unlock_irqrestore(&engine->lock, flags);
}

int xdma_threads_create(unsigned int num_threads)
{
	struct xdma_kthread *thp;
	int rv;
	int cpu;

	if (thread_cnt) {
		pr_warn("threads already created!");
		return 0;
	}

	pr_info("xdma_threads_create\n");

	cs_threads = kzalloc(num_threads * sizeof(struct xdma_kthread),
					GFP_KERNEL);
	if (!cs_threads)
		return -ENOMEM;

	/* N dma writeback monitoring threads */
	thp = cs_threads;
	for_each_online_cpu(cpu) {
		pr_debug("index %d cpu %d online\n", thread_cnt, cpu);
		thp->cpu = cpu;
		thp->timeout = 0;
		thp->fproc = xdma_thread_cmpl_status_proc;
		thp->fpending = xdma_thread_cmpl_status_pend;
		rv = xdma_kthread_start(thp, "cmpl_status_th", thread_cnt);
		if (rv < 0)
			goto cleanup_threads;

		thread_cnt++;
		if (thread_cnt == num_threads)
			break;
		thp++;
	}

	return 0;

cleanup_threads:
	kfree(cs_threads);
	cs_threads = NULL;
	thread_cnt = 0;

	return rv;
}

void xdma_threads_destroy(void)
{
	int i;
	struct xdma_kthread *thp;

	if (!thread_cnt)
		return;

	/* N dma writeback monitoring threads */
	thp = cs_threads;
	for (i = 0; i < thread_cnt; i++, thp++)
		if (thp->fproc)
			xdma_kthread_stop(thp);

	kfree(cs_threads);
	cs_threads = NULL;
	thread_cnt = 0;
}
