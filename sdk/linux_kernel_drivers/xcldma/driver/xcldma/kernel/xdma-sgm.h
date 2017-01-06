/**
 * Driver module exercising scatterlist interfaces
 *
 * (C) Copyright 2008-2014 Leon Woestenberg  <leon@sidebranch.com>
 *
 */

#include <linux/pagemap.h>
#include <linux/scatterlist.h>

/* describes a mapping from a virtual memory user buffer to scatterlist */
struct sg_mapping_t {
	/* scatter gather list used to map in the relevant user pages */
	struct scatterlist *sgl;
	/* pointer to array of page pointers */
	struct page **pages;
	/* maximum amount of pages in the scatterlist and page array */
	int max_pages;
	/* current amount of mapped pages in the scatterlist and page array */
	int mapped_pages;
};

struct sg_mapping_t *sg_create_mapper(unsigned long max_len);
void sg_destroy_mapper(struct sg_mapping_t *sgm);

int sgm_get_user_pages(struct sg_mapping_t *sgm, const char *start, size_t count, int to_user);
int sgm_put_user_pages(struct sg_mapping_t *sgm, int dirtied);
void sgm_dirty_pages(struct sg_mapping_t *sgm);

int sgm_kernel_pages(struct sg_mapping_t *sgm, const char *start, size_t count, int to_user);


