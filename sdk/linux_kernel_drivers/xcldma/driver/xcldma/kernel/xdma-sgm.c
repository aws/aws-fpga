/**
 * Driver module exercising scatterlist interfaces
 *
 * (C) Copyright 2008-2014 Leon Woestenberg  <leon@sidebranch.com>
 *
 */

//#define DEBUG

#include <linux/cdev.h>
#include <linux/dma-mapping.h>
#include <linux/init.h>
#include <linux/interrupt.h>
#include <linux/io.h>
#include <linux/jiffies.h>
#include <linux/kernel.h>
#include <linux/mm.h>
#include <linux/module.h>
#include <linux/pci.h>
#include <linux/sched.h>
#include <linux/slab.h>
#include <linux/types.h>

#include <asm/byteorder.h>
#include <asm/cacheflush.h>
#include <asm/delay.h>
#include <asm/pci.h>

#include "xdma-sgm.h"

/*
 * sg_create_mapper() - Create a mapper for virtual memory to scatterlist.
 *
 * @max_len: Maximum number of bytes that can be mapped at a time.
 *
 * Allocates a book keeping structure, array to page pointers and a scatter
 * list to map virtual user memory into.
 *
 */
struct sg_mapping_t *sg_create_mapper(unsigned long max_len)
{
	struct sg_mapping_t *sgm;
	if (max_len == 0)
		return NULL;
	/* allocate bookkeeping */
	sgm = kcalloc(1, sizeof(struct sg_mapping_t), GFP_KERNEL);
	if (sgm == NULL)
		return NULL;
	/* upper bound of pages */
	sgm->max_pages = max_len / PAGE_SIZE + 2;
	/* allocate an array of struct page pointers */
	sgm->pages = kcalloc(sgm->max_pages, sizeof(*sgm->pages), GFP_KERNEL);
	if (sgm->pages == NULL) {
		kfree(sgm);
		return NULL;
	}
	pr_debug("Allocated %lu bytes for page pointer array for %d pages @0x%p.\n",
		sgm->max_pages * sizeof(*sgm->pages), sgm->max_pages, sgm->pages);
	/* allocate a scatter gather list */
	sgm->sgl = kcalloc(sgm->max_pages, sizeof(struct scatterlist), GFP_KERNEL);
	if (sgm->sgl == NULL) {
		kfree(sgm->pages);
		kfree(sgm);
		return NULL;
	}
	pr_debug("Allocated %lu bytes for scatterlist for %d pages @0x%p.\n",
		sgm->max_pages * sizeof(struct scatterlist), sgm->max_pages, sgm->sgl);
	sg_init_table(sgm->sgl, sgm->max_pages);
	pr_debug("sg_mapping_t *sgm=0x%p\n", sgm);
	pr_debug("sgm->pages=0x%p\n", sgm->pages);
	return sgm;
};

/*
 * sg_destroy_mapper() - Destroy a mapper for virtual memory to scatterlist.
 *
 * @sgm scattergather mapper handle.
 */
void sg_destroy_mapper(struct sg_mapping_t *sgm)
{
	/* user failed to call sgm_unmap_user_pages() */
	BUG_ON(sgm->mapped_pages > 0);
	/* free scatterlist */
	kfree(sgm->sgl);
	/* free page array */
	kfree(sgm->pages);
	/* free mapper handle */
	kfree(sgm);
	pr_debug("Freed page pointer and scatterlist.\n");
};

/*
 * sgm_map_user_pages() - Get user pages and build a scatterlist.
 *
 * @sgm scattergather mapper handle.
 * @start User space buffer (virtual memory) address.
 * @count Number of bytes in buffer.
 * @to_user !0 if data direction is from device to user space.
 *
 * Returns Number of entries in the table on success, -1 on error.
 */
int sgm_get_user_pages(struct sg_mapping_t *sgm, const char *start, size_t count, int to_user)
{
	/* calculate page frame number @todo use macro's */
	const unsigned long first = ((unsigned long)start & PAGE_MASK) >> PAGE_SHIFT;
	const unsigned long last  = (((unsigned long)start + count - 1) & PAGE_MASK) >> PAGE_SHIFT;

	/* the number of pages we want to map in */
	const int nr_pages = last - first + 1;
	int rc, i;
	struct scatterlist *sgl = sgm->sgl;
	/* pointer to array of page pointers */
	struct page **pages = sgm->pages;

	pr_debug("sgm_map_user_pages()\n");
	pr_debug("sgl = 0x%p.\n", sgl);

	/* no pages should currently be mapped */
	BUG_ON(sgm->mapped_pages > 0);
	if (start + count < start)
		return -EINVAL;
	if (nr_pages > sgm->max_pages)
		return -EINVAL;
	if (count == 0)
		return 0;
	/* initialize scatter gather list */
	sg_init_table(sgl, nr_pages);

	pr_debug("pages=0x%p\n", pages);
	pr_debug("start = 0x%llx.\n",
		(unsigned long long)start);
	pr_debug("first = %lu, last = %lu\n", first, last);

	for (i = 0; i < nr_pages - 1; i++) {
		pages[i] = NULL;
	}
	/* try to fault in all of the necessary pages */
        rc = get_user_pages_fast((unsigned long)start, nr_pages, to_user/*write*/, pages);
	pr_debug("get_user_pages_fast(%lu, nr_pages = %d) == %d.\n", (unsigned long)start, nr_pages, rc);

	for (i = 0; i < nr_pages - 1; i++) {
		pr_debug("%04d: page=0x%p\n", i, pages[i]);
	}
	/* errors and no page mapped should return here */
	if (rc < nr_pages) {
		if (rc > 0) sgm->mapped_pages = rc;
		pr_debug("Could not get_user_pages(), %d.\n", rc);
		goto out_unmap;
	}
	/* XXX */
	BUG_ON(rc != nr_pages);
	sgm->mapped_pages = rc;
	pr_debug("sgm->mapped_pages = %d\n", sgm->mapped_pages);

	/* XXX: scsi/st.c is mentioning this as FIXME */
	for (i = 0; i < nr_pages; i++) {
		flush_dcache_page(pages[i]);
	}

	/* populate the scatter/gather list */
	pr_debug("%04d: page=0x%p\n", 0, (void *)pages[0]);

	sg_set_page(&sgl[0], pages[0], 0 /*length*/, offset_in_page(start));
	pr_debug("sg_page(&sgl[0]) = 0x%p (pfn = %lu).\n", sg_page(&sgl[0]),
		page_to_pfn(sg_page(&sgl[0])));

	/* verify if the page start address got into the first sg entry */
	pr_debug("sg_dma_address(&sgl[0])=0x%016llx.\n", (u64)sg_dma_address(&sgl[0]));
	pr_debug("sg_dma_len(&sgl[0])=0x%08x.\n", sg_dma_len(&sgl[0]));

	/* multiple pages? */
	if (nr_pages > 1) {
		/* offset was already set above */
		sgl[0].length = PAGE_SIZE - sgl[0].offset;
		pr_debug("%04d: page=0x%p, pfn=%lu, offset=%u, length=%u (FIRST)\n", 0,
			(void *)sg_page(&sgl[0]), (unsigned long)page_to_pfn(sg_page(&sgl[0])), sgl[0].offset, sgl[0].length);
		count -= sgl[0].length;
		/* iterate over further pages, except the last page */
		for (i = 1; i < nr_pages - 1; i++) {
			BUG_ON(count < PAGE_SIZE);
			/* set the scatter gather entry i */
			sg_set_page(&sgl[i], pages[i], PAGE_SIZE, 0/*offset*/);
			count -= PAGE_SIZE;
			pr_debug("%04d: page=0x%p, pfn=%lu, offset=%u, length=%u\n", i,
				(void *)sg_page(&sgl[i]), (unsigned long)page_to_pfn(sg_page(&sgl[i])), sgl[i].offset, sgl[i].length);
		}
		/* last page */
		BUG_ON(count > PAGE_SIZE);
		/* set count bytes at offset 0 in the page */
		sg_set_page(&sgl[i], pages[i], count, 0);
		pr_debug("%04d: page=0x%p, pfn=%lu, offset=%u, length=%u (LAST)\n", i,
			(void *)sg_page(&sgl[i]), (unsigned long)page_to_pfn(sg_page(&sgl[i])), sgl[i].offset, sgl[i].length);
	}
	/* single page */
	else {
		/* limit the count */
		sgl[0].length = count;
		pr_debug("%04d: page=0x%p, pfn=%lu, offset=%u, length=%u (SINGLE/FIRST/LAST)\n", 0,
			(void *)sg_page(&sgl[i]), (unsigned long)page_to_pfn(sg_page(&sgl[0])), sgl[0].offset, sgl[0].length);
	}
	return nr_pages;

out_unmap:
	/* { rc < 0 means errors, >= 0 means not all pages could be mapped } */
	/* did we map any pages? */
	for (i = 0; i < sgm->mapped_pages; i++)
		put_page(pages[i]);
	rc = -ENOMEM;
	sgm->mapped_pages = 0;
	return rc;
}

/*
 * sgm_unmap_user_pages() - Mark the pages dirty and release them.
 *
 * Pages mapped earlier with sgm_map_user_pages() are released here.
 * after being marked dirtied by the DMA.
 *
 */
int sgm_put_user_pages(struct sg_mapping_t *sgm, int dirtied)
{
	int i;
	/* mark page dirty */
	if (dirtied)
		sgm_dirty_pages(sgm);
	/* put (i.e. release) pages */
	for (i = 0; i < sgm->mapped_pages; i++) {
		put_page(sgm->pages[i]);
	}
	/* remember we have zero pages */
	sgm->mapped_pages = 0;
	return 0;
}

void sgm_dirty_pages(struct sg_mapping_t *sgm)
{
	int i;
	/* iterate over all mapped pages */
	for (i = 0; i < sgm->mapped_pages; i++) {
		/* mark page dirty */
		SetPageDirty(sgm->pages[i]);
	}
}

/* sgm_kernel_pages() -- create a sgm map from a vmalloc()ed memory */
int sgm_kernel_pages(struct sg_mapping_t *sgm, const char *start, size_t count, int to_user)
{
	/* calculate page frame number @todo use macro's */
	const unsigned long first = ((unsigned long)start & PAGE_MASK) >> PAGE_SHIFT;
	const unsigned long last  = (((unsigned long)start + count - 1) & PAGE_MASK) >> PAGE_SHIFT;

	/* the number of pages we want to map in */
	const int nr_pages = last - first + 1;
	int rc, i;
	struct scatterlist *sgl = sgm->sgl;
	/* pointer to array of page pointers */
	struct page **pages = sgm->pages;
	unsigned char *virt = (unsigned char *)start;

	pr_debug("sgm_kernel_pages()\n");
	pr_debug("sgl = 0x%p.\n", sgl);

	/* no pages should currently be mapped */
	BUG_ON(sgm->mapped_pages > 0);
	if (start + count < start)
		return -EINVAL;
	if (nr_pages > sgm->max_pages)
		return -EINVAL;
	if (count == 0)
		return 0;
	/* initialize scatter gather list */
	sg_init_table(sgl, nr_pages);

	pr_debug("pages=0x%p\n", pages);
	pr_debug("start = 0x%llx.\n",
		(unsigned long long)start);
	pr_debug("first = %lu, last = %lu\n", first, last);

	/* get pages belonging to vmalloc()ed space */
	for (i = 0; i < nr_pages; i++, virt += PAGE_SIZE) {
		pages[i] = vmalloc_to_page(virt);
		if (pages[i] == NULL)
			goto err;
		/* make sure page was allocated using vmalloc_32() */
		BUG_ON(PageHighMem(pages[i]));
	}
	for (i = 0; i < nr_pages; i++) {
		pr_debug("%04d: page=0x%p\n", i, pages[i]);
	}
	sgm->mapped_pages = nr_pages;
	pr_debug("sgm->mapped_pages = %d\n", sgm->mapped_pages);

	/* XXX: scsi/st.c is mentioning this as FIXME */
	for (i = 0; i < nr_pages; i++) {
		flush_dcache_page(pages[i]);
	}

	/* populate the scatter/gather list */
	pr_debug("%04d: page=0x%p\n", 0, (void *)pages[0]);

	/* set first page */
	sg_set_page(&sgl[0], pages[0], 0 /*length*/, offset_in_page(start));
	pr_debug("sg_page(&sgl[0]) = 0x%p (pfn = %lu).\n", sg_page(&sgl[0]),
		page_to_pfn(sg_page(&sgl[0])));

	/* verify if the page start address got into the first sg entry */
	pr_debug("sg_dma_address(&sgl[0])=0x%016llx.\n", (u64)sg_dma_address(&sgl[0]));
	pr_debug("sg_dma_len(&sgl[0])=0x%08x.\n", sg_dma_len(&sgl[0]));

	/* multiple pages? */
	if (nr_pages > 1) {
		/* { sgl[0].offset is already set } */
		sgl[0].length = PAGE_SIZE - sgl[0].offset;
		pr_debug("%04d: page=0x%p, pfn=%lu, offset=%u length=%u (F)\n", 0,
			(void *)sg_page(&sgl[0]), (unsigned long)page_to_pfn(sg_page(&sgl[0])), sgl[0].offset, sgl[0].length);
		count -= sgl[0].length;
		/* iterate over further pages, except the last page */
		for (i = 1; i < nr_pages - 1; i++) {
			BUG_ON(count < PAGE_SIZE);
			/* set the scatter gather entry i */
			sg_set_page(&sgl[i], pages[i], PAGE_SIZE, 0/*offset*/);
			count -= PAGE_SIZE;
			pr_debug("%04d: page=0x%p, pfn=%lu, offset=%u length=%u\n", i,
				(void *)sg_page(&sgl[i]), (unsigned long)page_to_pfn(sg_page(&sgl[i])), sgl[i].offset, sgl[i].length);
		}
		/* last page */
		BUG_ON(count > PAGE_SIZE);
		/* 'count' bytes remaining at offset 0 in the page */
		sg_set_page(&sgl[i], pages[i], count, 0);
		pr_debug("%04d: pfn=%lu, offset=%u length=%u (L)\n", i,
			(unsigned long)page_to_pfn(sg_page(&sgl[i])), sgl[i].offset, sgl[i].length);
	}
	/* single page */
	else {
		/* limit the count */
		sgl[0].length = count;
		pr_debug("%04d: pfn=%lu, offset=%u length=%u (F)\n", 0,
			(unsigned long)page_to_pfn(sg_page(&sgl[0])), sgl[0].offset, sgl[0].length);
	}
	return nr_pages;

err:
	rc = -ENOMEM;
	sgm->mapped_pages = 0;
	return rc;
}
