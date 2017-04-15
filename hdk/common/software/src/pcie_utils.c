// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.

#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <stdlib.h>
#include <unistd.h>
#include <time.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <dirent.h>

#define MAP_SIZE    (64 * 1024)
#define MAX_SLOT    8
#define VENDOR_ID   0x1d0f
#define DEVICE_ID   0x1040

static char *	pcie_find_first(void);
static int	pcie_find_all(char *[], int);

//static uint64_t   g_bar0;
//static uintptr_t  g_base;
static __thread uint64_t    t_bar0;
static __thread uintptr_t   t_base;

static int pcie_count;
static char *pcie_ids[MAX_SLOT] = {
};

static void
pcie_report(char *name)
{
    //printf("using [%s]\n", name);
}

static char *
pcie_lookup(int slot)
{
    pcie_count = pcie_find_all(pcie_ids, MAX_SLOT);
    if (slot < 0 || slot >= pcie_count) {
        return NULL;
    }
    pcie_report(pcie_ids[slot]);
    return pcie_ids[slot];
}

static int
pcie_open_config(char *id)
{
    char buffer[128];

    sprintf(buffer, "/sys/bus/pci/devices/%s/config", id);

    int fd = open(buffer, O_RDWR);
    if (fd < 0) {
        //perror(buffer);
        return -1;
    }
    return fd;
}

static bool
pcie_check_device(char *id)
{
    int fd = pcie_open_config(id);
    if (fd < 0)
        return false;

    uint16_t vid, did;
    lseek(fd, 0, SEEK_SET);
    read(fd, &vid, sizeof(vid));
    read(fd, &did, sizeof(did));
    if (vid != VENDOR_ID || did != DEVICE_ID) {
        close(fd);
        return false;
    }

    uint8_t htype;
    lseek(fd, 0xe, SEEK_SET);
    read(fd, &htype, sizeof(htype));
    if ((htype & 0x7f) != 0x00) {
        close(fd);
        return false;
    }

    // Fix problem with config space so device can be memory mapped
    uint8_t patch = 0x7;
    lseek(fd, 4, SEEK_SET);
    write(fd, &patch, 1);
    close(fd);

    return true;
}

static int
pcie_find_all(char *ids[], int max)
{
    char *base = "/sys/bus/pci/devices";
    DIR *d = opendir(base);
    if (d == NULL) {
        perror(base);
        return 0;
    }

    int count = 0;
    for (;;) {
        static struct dirent de;
        struct dirent *dp;
        readdir_r(d, &de, &dp);
        if (dp == NULL)
            break;

        if (pcie_check_device(de.d_name)) {
            if ((ids[count] = strdup(de.d_name)) != NULL) {
                count++;
            }
        }
    }
    closedir(d); 
    return count;
}

static char *
pcie_find_first(void)
{
    char *base = "/sys/bus/pci/devices";
    DIR *d = opendir(base);
    if (d == NULL) {
        perror(base);
        return NULL;
    }
    for (;;) {
        static struct dirent de;
        struct dirent *dp;
        readdir_r(d, &de, &dp);
        if (dp == NULL)
            break;

        if (pcie_check_device(de.d_name)) {
            closedir(d);
            pcie_report(de.d_name);
            return de.d_name;
        }
    }
    closedir(d); 
    return NULL;
}

static bool
pcie_mmap(char *id, bool verify)
{
    if (verify && !pcie_check_device(id)) {
        return false;
    }

    int fd = pcie_open_config(id);
    if (fd < 0) {
        return false;
    }
    
    lseek(fd, 0x10, SEEK_SET);
    read(fd, &t_bar0, sizeof(t_bar0));
    if (t_bar0 == 0) {
        close(fd);
        return false;
    }
    close(fd);
    uint8_t flags = t_bar0 & 0xf;
    if ((flags & 0x06) == 0) {
        // 32bit BAR
        t_bar0 &= 0xfffffff0;
    } else {
        // 64bit BAR
        t_bar0 &= ~0xf;
    }

    fd = open("/dev/mem", O_RDWR | O_SYNC);
    if (fd == -1) {
        perror("/dev/mem");
        return false;
    }
    
    t_base = (uintptr_t) mmap(0, MAP_SIZE, PROT_READ|PROT_WRITE, MAP_SHARED, fd, t_bar0);
    if (t_base == (uintptr_t) MAP_FAILED) {
        perror("mmap");
        return false;
    }

    return true;
}

void
poke(uint32_t addr, uint32_t value)
{
   *(uint32_t *) (t_base + addr) = value;
}

uint32_t
peek(uint32_t addr)
{
   uint32_t v = *(uint32_t *) (t_base + addr);
   return v;
}

bool
pcie_connect(int *argcP, char ***argvP)
{
    bool verify = true;
    char *id = NULL;
    int ac = *argcP;
    char **av = *argvP;

    while (ac > 1) {
        char *arg = av[1];
        if (arg[0] != '-' || arg[1] == 0)
            break;
        if (arg[1] != 's' && arg[1] != 'S' && arg[1] != 'T')
            break;
        ac--;
        av++;

        char *opt;
        if (arg[2] == 0) {
            if (ac <= 1) {
                break;
            }
            opt = av[1];
            ac--;
            av++;
        } else {
            opt = &arg[2];
        }

        int slot;
        switch (arg[1]) {
        case 's':       // locate by domain:bus:device.func
            id = opt;
            verify = false;
            goto try_mmap;

        case 'S':       // locate by slot number
            slot = strtol(opt, NULL, 0);
            id = pcie_lookup(slot);
            goto try_mmap;

//      case 'T': {
//          int t = strtol(opt, NULL, 0);
//          timeout_set(t);
//          break;
//      }
        }
    }

    // no arguments given
    id = pcie_find_first();

try_mmap:
    if (id == NULL)
        return false;
    *argcP = ac;
    *argvP = av;
    return pcie_mmap(id, verify);
}

uint64_t
pcie_bar0(void)
{
    return t_bar0;
}

uint32_t
pcie_bar0_size(void)
{
    return MAP_SIZE;
}

void
pcie_set_debug(bool enable)
{
}
