/*
 * Amazon FPGA Hardware Development Kit
 *
 * Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Amazon Software License (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *    http://aws.amazon.com/asl/
 *
 * or in the "license" file accompanying this file. This file is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <fpga_pci.h>
#include <fpga_mgmt.h>
#include <utils/lcd.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

#include "fpga_mgmt_tests.h"

static void *test_slot_spec(void *arg);
static void *test_all_slot_specs(void *arg);

struct thread 
{
    /* thread information */
    pthread_t thread;
    int id;

    /* thread arguments */
    struct fpga_slot_spec *spec_array;
    int slot;

    /* thread result */
    int rc;
    char message[256];
};

/* copied from fpga_pci_sysfs.c */
#if defined(_BSD_SOURCE) || defined(_SVID_SOURCE)
#   define USE_READDIR_R
#endif

int fpga_mgmt_test_readdir(unsigned int num_threads)
{
    int rc;
    int num_slots;
    struct thread *threads = NULL;

#if defined(USE_READDIR_R)
    log_info("Using readdir_r because glibc is old.");
#else
    log_info("Using readdir because readdir_r is deprecated.");
#endif

    struct fpga_slot_spec spec_array[FPGA_SLOT_MAX];
    memset(spec_array, 0, sizeof(spec_array));
    rc = fpga_pci_get_all_slot_specs(spec_array, sizeof_array(spec_array));
    fail_on(rc, out, "fpga_pci_get_all_slot_specs failed");

    num_slots = FPGA_SLOT_MAX;
    for (int i = 0; i < FPGA_SLOT_MAX; ++i) {
        if (spec_array[i].map[FPGA_APP_PF].vendor_id == 0) {
            num_slots = i;
            break;
        }
    }

    if (num_threads == 0) {
        num_threads = 512;
    }
    if (num_threads > 4096) {
        num_threads = 4096;
    }
    threads = calloc(num_threads, sizeof(struct thread));

    void *(*thread_start_funcs[2])(void *) = {
        test_slot_spec, test_all_slot_specs };

    for (int i = 0; i < num_threads; ++i) {
        threads[i].id = i;
        threads[i].spec_array = spec_array;
        threads[i].slot = (i % (num_slots * 2)) / 2;
        rc = pthread_create(&threads[i].thread, NULL, thread_start_funcs[i % 2],
                            &threads[i]);
        fail_on(rc, out, "failed to create a thread");
    }

    bool test_passed = true;
    for (int i = 0; i < num_threads; ++i) {
        void *thread_result;
        rc = pthread_join(threads[i].thread, &thread_result);
        fail_on(rc, out, "pthread_join failed");

        if (&threads[i] != thread_result) {
            log_error("the result wasn't expected on # %d\n", i);
        }

        struct thread *thread = thread_result;
        if (thread->rc != 0) {
            log_error("thread id: %d failed with: %s\n", thread->id,
                thread->message);
            test_passed = false;
        }
    }

    log_info("test completed with %d threads, result: %s\n", num_threads,
        (test_passed) ? "passed" : "failed");
    if (!test_passed) {
        rc = -1;
    }

out:
    if (threads != NULL) {
        free(threads);
    }
    return rc;
}

static void show_slot_spec(struct fpga_slot_spec *spec, char *message, int size)
{
    snprintf(message, size, "dbdf: %04x:%02x:%02x.%x\n", (int) spec->map[0].domain,
        (int) spec->map[0].bus, (int) spec->map[0].dev, (int) spec->map[0].func);
}

static void *test_slot_spec(void *arg)
{
    int rc;
    struct fpga_slot_spec spec;
    struct thread *thread = arg;

    rc = fpga_pci_get_slot_spec(thread->slot, &spec);
    if (rc != 0) {
        snprintf(thread->message, sizeof(thread->message),
            "unabled to read slot spec on slot %d", thread->slot);
        goto out;
    }

    if (memcmp(&spec, &thread->spec_array[thread->slot], sizeof(spec)) != 0) {
        rc = -1;
        show_slot_spec(&spec, thread->message, sizeof(thread->message));
    }

out:
    thread->rc = rc;
    return thread;
}

static void *test_all_slot_specs(void *arg)
{
    int rc;
    struct thread *thread = arg;
    struct fpga_slot_spec spec_array[FPGA_SLOT_MAX];
    memset(spec_array, 0, sizeof(spec_array));

    rc = fpga_pci_get_all_slot_specs(spec_array, sizeof_array(spec_array));
    if (rc != 0) {
        snprintf(thread->message, sizeof(thread->message),
            "unabled to read all slot specs");
        goto out;
    }

    if (memcmp(spec_array, thread->spec_array, sizeof(spec_array)) != 0) {
        rc = -1;
        snprintf(thread->message, sizeof(thread->message),
            "slot spec array failed comparison test");
    }

out:
    thread->rc = rc;
    return thread;
}
