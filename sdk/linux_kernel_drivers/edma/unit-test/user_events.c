#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <poll.h>

#ifndef PAGE_SIZE
#define PAGE_SIZE (1024 *4)
#endif

#define  SIZE_OF_DATA (10 * PAGE_SIZE)
#define CHUNK_SIZE (PAGE_SIZE)

char* write_buf;
char* read_buf;
long long int write_index;
long long int read_index;

bool read_done = false;

static char *rand_string(char *str, size_t size)
{
    const char charset[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRTSUVWXYZ1234567890";
    int i;

    for(i = 0; i < size; i++){
        int key = rand() % (int) (sizeof charset - 1);
        str[i] = charset[key];
    }

    str[size-1] = '\0';

    return str;
}

int main()
{

    int fd, i, ret;
    int write_size = 0x1000;
    int interrupt_occured =0 ;
    srand ( time(NULL) );

    if((fd = open("/dev/fpga5_event0",O_RDWR)) == -1){
        perror("open failed");
        return -1;
    }

    //polling on event4 and event6

    struct pollfd fds[] = {
        { fd, POLLIN },
    };

    while(!interrupt_occured)
    {
	    sleep(5);

	    int r = poll(fds, 1, 0);
	    if (r < 0) {
		    /* ... there was an error! ... */
	    } else {
		    if(fds[0].revents & POLLIN) {
			    interrupt_occured = 1;
			    printf("Event for fd0 was triggered.");
			    /* ... event4 (fd4) was triggered!! ... */
		    }
		    //
		    //        if(fds[1].revents & POLLIN) {
		    //          /* ... event4 (fd6) was triggered!! ... */
		    //        }
	    }
    }

    close(fd);

    return 0;
}


