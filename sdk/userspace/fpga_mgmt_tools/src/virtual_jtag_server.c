/*
 * Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#define _CRT_SECURE_NO_WARNINGS 1

#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <malloc.h>


#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/tcp.h>
#include <netdb.h>
#include <unistd.h>
#include <string.h>

#include <sys/time.h>

#include <fpga_pci.h>
#include "virtual_jtag.h"

#define MAX_PACKET_LEN 10000

#define tostr2(X) #X
#define tostr(X) tostr2(X)

#ifndef XVC_VERSION
#define XVC_VERSION 10
#endif

static unsigned max_packet_len = MAX_PACKET_LEN;

static XvcClient xvc_client;

static unsigned char *reply_buf = NULL;
static unsigned reply_max = 0;
static unsigned reply_len;

static void reply_buf_size(unsigned bytes) {
    if (reply_max < bytes) {
        if (reply_max == 0) reply_max = 1;
        while (reply_max < bytes) reply_max *= 2;
        reply_buf = (unsigned char *)realloc(reply_buf, reply_max);
    }
}


static int closesocket(int sock)
{
    return close(sock);
}

static int open_server(const char* tcp_port) {
    int err = 0;
    int sock = -1;
    struct addrinfo hints;
    struct addrinfo * reslist = NULL;
    struct addrinfo * res = NULL;

    memset(&hints, 0, sizeof hints);
    hints.ai_family = PF_INET;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;
    hints.ai_flags = AI_PASSIVE;
    err = getaddrinfo(NULL, tcp_port, &hints, &reslist);
    if (err) {
        fprintf(stderr, "getaddrinfo: %s\n", gai_strerror(err));
        errno = EINVAL;
        return FPGA_ERR_FAIL;
    }

    for (res = reslist; res != NULL; res = res->ai_next) {
        const int i = 1;
        sock = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
        if (sock < 0) continue;

        err = 0;
        if (setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, (char *)&i, sizeof(i)) < 0) err = 1;
        if (!err && bind(sock, res->ai_addr, res->ai_addrlen)) err = 1;
        if (!err && listen(sock, 4)) err = 1;
        if (!err) break;

        closesocket(sock);
        sock = -1;
    }
    freeaddrinfo(reslist);
    return sock;
}

static unsigned get_uint_le(void * buf, int len) {
    unsigned char * p = (unsigned char *)buf;
    unsigned value = 0;

    while (len-- > 0) {
        value = (value << 8) | p[len];
    }
    return value;
}

static void set_uint_le(void * buf, int len, unsigned value) {
    unsigned char * p = (unsigned char *)buf;

    while (len-- > 0) {
        *p++ = (unsigned char)value;
        value >>= 8;
    }
}


static int send_packet(XvcClient * c, const void * buf, unsigned len) {
    int rval = send(c->fd, buf, len, 0);
    return rval;
}

static void consume_packet(XvcClient * c, unsigned len) {
    assert(len <= c->buf_len);
    c->buf_len -= len;
    memmove(c->buf, c->buf + len, c->buf_len);
}


static void read_packet(XvcClient * c) {
    unsigned char * cbuf;
    unsigned char * cend;
    unsigned fill;

    reply_buf_size(max_packet_len);


    struct timeval stop, start;

read_more:

    cbuf = c->buf;
    cend = cbuf + c->buf_len;
    fill = 0;
    reply_len = 0;
    for (;;) {
        unsigned char * p = cbuf;
        unsigned char * e = p + 30 < cend ? p + 30 : cend;
        int len;

        while (p < e && *p != ':') {
            // printf("cycle: %d at %x ", *p, p);
            p++;
        }
        if (p >= e) {
            if (p - cbuf >= 30) {
                fprintf(stderr, "protocol error: received %.30s\n", cbuf);
                goto error;
            }
            fill = 1;
            break;
        }
        p++;
        len = p - cbuf;

        if (len == 8 && memcmp(cbuf, "getinfo:", len) == 0) {
            snprintf((char *)reply_buf + reply_len, 100, "xvcServer_v%u.%u:%u\n",
                     XVC_VERSION / 10, XVC_VERSION % 10, c->buf_max);
            reply_len += strlen((char *)reply_buf + reply_len);
            goto reply;
        }



        if (len == 6 && memcmp(cbuf, "shift:", len) == 0) {

            gettimeofday(&start, NULL);

            unsigned bits;
            unsigned bytes;

            if (cend < p + 4) {
                fill = 1;
                break;
            }
            bits = get_uint_le(p, 4);
            bytes = (bits + 7) / 8;
            if (cend < p + 4 + bytes * 2) {
                assert(p + 4 + bytes * 2 - cbuf <= c->buf_max);
                fill = 1;
                break;
            }
            p += 4;

            if (!c->pending_error[0]) {
                // fprintf(stdout, "bits received %d %d %x %x\n", bits, bytes, p[0], p[bytes]);
        
                shift_tms_tdi(c->jtag_pci_bar, bits, p, p + bytes, reply_buf + reply_len);
            }
            if (c->pending_error[0]) {
                printf("Problem\n");
                memset(reply_buf + reply_len, 0, bytes);
            }
            reply_len += bytes;
            p += bytes * 2;

            gettimeofday(&stop, NULL);
            //printf("Shift external %lu u-seconds\n", stop.tv_usec - start.tv_usec);

            goto reply_with_optional_status;
        }

        if (len == 7 && memcmp(cbuf, "settck:", len) == 0) {
            unsigned long nsperiod;
            unsigned long resnsperiod;

            if (cend < p + 4) {
                fill = 1;
                break;
            }
            nsperiod = get_uint_le(p, 4);
            p += 4;

            if (!c->pending_error[0])
                set_tck(nsperiod, &resnsperiod);
            if (c->pending_error[0])
                resnsperiod = nsperiod;

            set_uint_le(reply_buf + reply_len, 4, resnsperiod);
            reply_len += 4;
            goto reply_with_optional_status;
        }



        // fprintf(stderr, "protocol error: received len %d", (int)len);
        fprintf(stderr, "protocol error: received %.*s\n", (int)len, cbuf);
        goto error;

    reply_with_optional_status:
        // printf("Here2\n");
        if (!c->enable_status) goto reply;

    reply:
        cbuf = p;
    }

    if (c->buf < cbuf) {

        if (send_packet(c, reply_buf, reply_len) < 0) goto error;
        consume_packet(c, cbuf - c->buf);
        
        gettimeofday(&stop, NULL);
        // if (start.tv_usec != 0)
        //     printf("Shift send packet %lu u-seconds\n", stop.tv_usec - start.tv_usec);
        
        if (c->buf_len && !fill) goto read_more;
    }

    {
        int len = recv(c->fd, c->buf + c->buf_len, c->buf_max - c->buf_len, 0);
        if (len > 0) {
            c->buf_len += len;
            goto read_more;
        }
        if (len < 0) goto error;
    }
    return;

error:
    fprintf(stderr, "XVC connection terminated: error %d\n", errno);
}

int xvcserver_start(
    uint32_t slot_id,
    char* tcp_port)
{
    XvcClient * c = &xvc_client;
    pci_bar_handle_t jtag_pci_bar;
    int sock;
    int fd;

   


    sock = open_server(tcp_port);
    if (sock < 0) {
        //perror("failed to create socket, for tcp port %s", tcp_port);
        return 1;
    }

    while ((fd = accept(sock, NULL, NULL)) >= 0) {
        int opt = 1;

        if (setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, (char *)&opt, sizeof(opt)) < 0)
            fprintf(stderr, "setsockopt TCP_NODELAY failed\n");

        if (open_port(slot_id, &jtag_pci_bar) ) {
            fprintf(stderr, "open Virtual JTAG over PCIe failed\n");
            closesocket(fd);
            continue;
        }

        memset(c, 0, sizeof *c);
        c->fd = fd;
        c->jtag_pci_bar = jtag_pci_bar;
        c->buf_max = max_packet_len;
        c->buf = (uint8_t *)malloc(c->buf_max);
        read_packet(c);
        close_port(jtag_pci_bar);
        closesocket(fd);
        free(c->buf);
    }

    closesocket(sock);
    return 0;
}
