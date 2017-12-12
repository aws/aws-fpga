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
#define NUMBER_OF_ITERATIONS (10*1024)
#define INITIAL_DATA_SIZE (4096)

char* write_buf;
char* read_buf;
long long int write_index;
long long int read_index;

bool read_done = false;

static char *rand_string(char *str, size_t size)
{
	const char charset[] = "123456789";
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
	srand ( time(NULL) );
	int write_size = INITIAL_DATA_SIZE;

	write_buf = (char*)malloc(sizeof(char) * 10 * 1024*1024);
	read_buf = (char*)malloc(sizeof(char) * 10 * 1024*1024);


	rand_string(write_buf, SIZE_OF_DATA);

	if((fd = open("/dev/edma0_queue_0",O_RDWR)) == -1){
		perror("open failed");
		return -1;
	}
	while(1) {


		system("dmesg -C");

		printf("Doing size %d\n", write_size);

		for( i = 0; i < NUMBER_OF_ITERATIONS ; i++ )
		{
			int data_size = write_size;

			ret = lseek(fd, 0x010000000, SEEK_SET);
			if(ret < 0)
				exit(3);

			ret = write(fd, write_buf, data_size);

			ret = fsync(fd);

			ret = lseek(fd, 0x010000000, SEEK_SET);

			ret = read(fd, read_buf, data_size);

			if(!memcmp(write_buf, read_buf, data_size)) {
//				printf("The string written and the string read are identicle!\n");
			} else {
				int i = 0;

				printf("Failed for data_size %d\n", data_size);

				printf("Data written is:\n");
				for(i = 0; i < data_size; i++) {
					printf("%c", write_buf[i]);
				}
				printf("\n");

				printf("Data read is:\n");
				for(i = 0; i < data_size; i++) {
					printf("%d:%c\n", i, read_buf[i]);
				}
				printf("\n");

				exit(-1);
			}

		}

		write_size = (write_size + 1) % (10 * 1024*1024);

	}

	free(write_buf);
	free(read_buf);

	return 0;
}


