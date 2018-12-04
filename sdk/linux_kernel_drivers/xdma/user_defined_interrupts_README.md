# Using AWS FPGA user-defined interrupts in C/C++ application

AWS FPGA provides options for Custom Logic (CL) to generate user-defined interrupt events, sent to the instance via MSI-X message.

At the hardware level, these interrupt event are defined in [AWS Shell Interface Specification](../../../hdk/docs/AWS_Shell_Interface_Specification.md)



## User-defined interrupts rely on the XDMA driver

The XDMA driver services both CL interrupt events and the DMA between instance's CPU memory and CL. 

For interrupt events, XDMA is responsible for:

i) Initialization of the MSI-X interrupt logic in the Shell to map cl_sh_apppf_int interrupts events to MSI-X interrupts of the PCIe AppPF

ii) Exposing all the interrupt events as file devices under `/dev/xdmaX_events_Y` where X is the slot-id and Y is the event/interrupt


iii) Exposing each interrupt as a file-descriptor for event polling in Linux userspace

iv) Guarantees graceful teardown in case of a userspace process crashes or improper termination


## Installation of XDMA Driver

Please follow the [XDMA driver installation guide](./xdma_install.md) for compiling and installing the driver.

The driver needs to be installed once, regardless of how many FPGA slots are available.



## Polling on User-defined Interrupt/Event

The next example shows how an application can register to two events (aka user-defined interrupts) on slot 0

```
  fd4=open(“/dev/xdma0_events_4”, O_RDONLY);
  fd6=open(“/dev/xdma0_events_6”, O_RDONLY);

  //polling on event4 and event6
  struct pollfd fds[] = {
      { fd4, POLLIN },
      { fd6, POLLIN }
  };

  int r = poll(fds, 2, 0);
  if (r < 0) {
      /* ... there was an error! ... */
  } else {
      if(fds[0].revents & POLLIN) {
        /* event4 (fd4) was triggered!! */
        read_fd = fd4;
      }
  
      if(fds[1].revents & POLLIN) {
        /* event6 (fd6) was triggered!! */
        read_fd = fd6;
      }
      /* read and clear the interrupt so we can detect future interrupts */
      uint32_t events_user;
      pread(read_fd, &events_user, sizeof(events_user), 0);
  }

  close(fd4);
  close(fd6);
```


# FAQ


**Q: How can I toggle an interrupt event from within the CL?**

Toggling of user interrupt event by toggling the `cl_sh_apppf_int_req` interface to an MSI-X, which gets translated to an event in Linux userspace that an application can poll() on. Follow [AWS Shell Interface Spec](../../../hdk/docs/AWS_Shell_Interface_Specification.md) for the hardware interface details.


**Q: How do I stop interrupts/events?**


To stop all the interrupts/events, one should disable the toggling of interrupt pins at the CL side (implementation specific).


**Q: How can I stop receiving interrupt events?**

There are three options to mask an interrupt/event:

i) An application can stop calling poll() on the event file-descriptor. The interrupt may still toggle, and the kernel XDMA driver is invoked, but the application in Linux userspace does not see it.

ii) Call close() for all the file descriptors associated with the specification interrupt/event, the XDMA driver masks the interrupt

iii) Control the interrupt request signals at the interrupt between the CL and Shell.


**Q: Where are the cause and mask bits for the user-defined interrupts?**

The cause and mask bits (if defined) are part of the CL and are implementation specific. In the example given in this file the XDMA driver provides a robust way to translate a interrupt request on the CL to Shell interface to Linux kernel and userspace. It should be considered as a message/event transfer mechanism.  Also see the test_dram_dma.c `interrupt_example()` for a full working example of user-defined interrupts.


**Q: Which MSI-X entries are used for the user-defined interrupts?**

The XDMA Linux kernel driver maps the CL user-defined interrupts to MSI-X entries (8 to 23), which are mapped to `/dev/xdmaX_events_Y`, where Y corresponds to the user-defined interrupt number (0 through 15).  This is handled by the XDMA driver and user intervention is not required.

**Q: How can I count how many interrupts/events happened?**

  Run `cat /proc/interrupts | grep xdma`.  The interrupt count shown corresponds to interrupts from the CL via the corresponding MSI-X.
  

**Q: Can the userspace application miss an interrupt event?**

Yes, that can happen if: 

i) The XDMA driver is not installed

ii) The interrupt was delivered to Linux while the corresponding file descriptor was not open by any process.


**Q: If I send multiple interrupt requests, do I need to poll() multiple times?**

It all depends on the timing when the interrupt request was sent and when the poll() is called.

The XDMA driver keeps a state per interrupt event that indicates it has been asserted from the last time a poll() was called.  If the same interrupt is sent by the CL multiple times before the poll() is called, the next call to the poll() indicates that there was an interrupt event, but it doesn't provide the interrupt count, and it doesn't keep a queue.

