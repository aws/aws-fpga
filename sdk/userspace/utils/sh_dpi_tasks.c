#include <utils/sh_dpi_tasks.h>

void host_memory_putc(uint64_t addr, uint8_t data)
{
  *(uint8_t *)addr = data;
}

//void host_memory_getc(uint64_t addr, uint8_t *data)
uint8_t host_memory_getc(uint64_t addr)
{
  return *(uint8_t *)addr;
}
void cosim_printf(const char *format, ...) 
{                                        
  static char sv_msg_buffer[256];        
  va_list args;                          

  va_start(args, format);                
  vsprintf(sv_msg_buffer, format, args); 
#ifdef SV_TEST
  sv_printf(sv_msg_buffer);                
#else
  printf(sv_msg_buffer); 
#endif

  va_end(args);                          
}

void int_handler(uint32_t int_num)
{
// Vivado does not support svGetScopeFromName
#ifndef VIVADO_SIM
  svScope scope;
  scope = svGetScopeFromName("tb");
  svSetScope(scope);
#endif

  cosim_printf("Received interrupt %2d", int_num);
  sv_int_ack(int_num);
}
