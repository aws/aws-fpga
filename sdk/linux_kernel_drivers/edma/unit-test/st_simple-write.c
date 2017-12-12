#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>

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
    srand ( time(NULL) );

    write_buf = (char*)malloc(sizeof(char) * SIZE_OF_DATA);
    read_buf = (char*)malloc(sizeof(char) * SIZE_OF_DATA);


    rand_string(write_buf, SIZE_OF_DATA);

    if((fd = open("/dev/edma0_queue_0",O_RDWR)) == -1){
        perror("open failed");
        return -1;   
    }

    ret = lseek(fd, 0x010000000, SEEK_SET);
    if(ret < 0)
    	exit(3);

    printf("----> %s\nwriting %u bytes\n", __func__, 121);
    ret = write(fd, write_buf, write_size);
    printf("Wrote %d bytes\n", ret);
    for(i = 0; i < 121; i++)
    {
        printf("%c", write_buf[i]);
    }
    printf("\n");

    ret = fsync(fd);

    ret = lseek(fd, 0x010000000, SEEK_SET);

    printf("\n---> %s\nTryting to read %d bytes\n", __func__, 79);
    ret = read(fd, read_buf, write_size);
    printf("Read %d bytes\n", ret);
    for(i = 0; i < 79; i++)
    {
        printf("%c", read_buf[i]);
    }
    printf("\n");


    if(!memcmp(write_buf, read_buf, write_size)){
        printf("The string written and the string read are identicle!\n");
    } else {
        int i = 0;

        printf("\nData written is:\n");
        for(i = 0; i <  write_size; i++)
        {
            printf("%c", write_buf[i]);
        }
        printf("\n");

        printf("\nData read is:\n");
        for(i = 0; i <  write_size; i++)
        {
            printf("%c", read_buf[i]);
        }
        printf("\n");

    }

    free(write_buf);
    free(read_buf);

    return 0;
}


