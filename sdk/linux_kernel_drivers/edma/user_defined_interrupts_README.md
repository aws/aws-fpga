# Using AWS FPGA user-defined interrupts in C/C++ application

AWS FPGA provides options for Custom Logic (CL) to generate user-defined interrupt events, sent to the instance via MSI-X message.

At the hardware level, these interrupt event are defined in [AWS Shell Interface Specification](../../../hdk/docs/AWS_Shell_Interface_Specification.md)



## User-defined interrupts relies on EDMA driver

AWS provides Elastic DMA (EDMA) (A reference Linux kernel driver) services both CL interrupt events and the DMA between instance's CPU memory and CL. 

For interrupt events, EDMA is responsible for:

i) Initialization of the MSI-X interrupt logic in the Shell to map cl_sh_apppf_int interrupts events to MSI-X interrupts of the PCIe AppPF

ii) Exposing all the interrupt events as file devices under /dev/fpgaX/eventY where X is the slot-id and Y is the event/interrupt


iii) Exposing each interrupt as a file-descriptor for event polling in Linux userspace

iv) Guarantees graceful teardown in case of a userspace process crashes or improper termination


## Installation of EDMA Driver

Please follow the [EDMA driver installation guide](./edma_install.md) for compiling and installing the driver.

The driver needs to be installed once, regardless of how many FPGA slots are available.



## Polling on User-defined Interrupt/Event

The next example shows how an application can register to two events (aka user-defined interrupts) on slot 0

```
  fd4=open(“/dev/fpga0_event4”, O_RDONLY);
  fd6=open(“/dev/fpga0_event6”, O_RDONLY);


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
        /* ... event4 (fd4) was triggered!! ... */
      }
  
      if(fds[1].revents & POLLIN) {
        /* ... event4 (fd6) was triggered!! ... */
      }
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

i) An application can stop calling poll() on the event file-descriptor. The interrupt may still toggle, and the kernel EDMA driver is invoked, but the application in Linux userspace does not see it.



ii) Call close() for all the file descriptors associated with the specification interrupt/event, the EDMA driver masks the interrupt

iii) Control the interrupt request signals at the interrupt between the CL and Shell.



**Q: Where are the cause and mask bits for the user-defined interrupts?**

The cause the mask bits, if exist, is part of the CL and are implementation specific. In the example(s) given in this file, and the EDMA driver provides a robust way to translate interrupts request on the CL to Shell interface to Linux kernel and userspace. It should be considered as a message/event transfer mechanism.



**Q: How can I count how many interrupts/events happened?**

  Run `cat /proc/interrupts` and look for fpgaX_eventY (where X is the slot-id and Y is the event/interrupt) for how many interrupts came from the CL via the corresponding MSI-X.
  
  Run `cat /TBD` shows how many times the userspace application called poll().



**Q: Can the userspace application miss an interrupt event?**


Yes, that can happen if: 
i) The EDMA driver is not installed

ii) The interrupt was delivered to Linux while the corresponding file descriptor was not open by any process.




**Q: If I send multiple interrupt requests, do I need to poll() multiple times?**

It all depends on the timing when the interrupt request was sent and when the poll() is called.

EDMA implementation keeps a state per interrupt event that indicates it has been asserted from the last time a poll() was called.  If the same interrupt is sent by the CL multiple times before the poll() is called, the next call to the poll() indicates that there was an interrupt event, but it doesn't provide the interrupt count, and it doesn't keep a queue.




**Q: Which MSI-X entries are used for the user-defined interrupts?**

The EDMA Linux kernel driver maps the CL user-defined interrupts to MSI-X entries 16 to 31, which is mapped to /dev/fpgaX/event0 through 15.  This is handled by the EDMA driver and user intervention is not required.
