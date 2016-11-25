#ifndef SH_DPI_TASKS
#define SH_DPI_TASKS

#include <stdarg.h>

extern void sv_printf(char *msg);
extern void sv_map_host_memory(char *memory);

extern void cl_peek(long long addr, int *data);
extern void cl_poke(long long addr, int  data);
extern void pause(int x);

int test_main(int *exit_code);

void host_memory_putc(long long addr, int data)
{
  *(char *)addr = (char)data;
}

void host_memory_getc(long long addr, int *data)
{
  *(char *)data = *(char *)addr;
}

void log_printf(const char *format, ...)
{
  static char sv_msg_buffer[256];
  va_list args;

  va_start(args, format);
  vsprintf(sv_msg_buffer, format, args);
  sv_printf(sv_msg_buffer);

  va_end(args);
}

#endif
