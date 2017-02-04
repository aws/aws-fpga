# Using AWS FPGA user-defined interrupts in C/C++ application

AWS FPGA provides options for CL (CustomLogic) in an AFI to generate user-defined interrupts.

At hardware level, these interrupts are defined in [AWS Shell Interface Specification](https://github.com/aws/aws-fpga/master/blob/hdl/docs/AWS_Shell_Interface_Specification.md)


# User-defined interrupts relies on EDMA driver

From software perspective, AWS provides reference linux kernel driver called EDMA (shared driver between the interrupts and the DMA) which is responsbile on:
1) Initializes the interrupt logic in the Shell to map user interrupts to MSI-X interrupts of the PCIe AppPF
2) Exposes all the interrupts as file devices under /dev/fpgaX/eventY where X is the slot-id and Y is the event/interrupt
3) Exposes each interrupt as file-descriptor for event polling in Linux userspace
4) guarantees graceful teardown in case of developer user space process crash or improper termination


## Installation of EDMA Driver

Please follow the [EDMA driver installation guide](./edma.md) for compiling and installing the driver.
The driver need to be installed once, regardless of how many FPGA slots are available



#  How Can an Application Use User-Defined Interrupts / Events ?



## Polling on User-defined Interrupt/Event

The next example shows how an application can register to two events (aka user-defined interrupts) on slot 0

```
  fd4=open(“/dev/fpga0/event4”, R);
  fd6=open(“/dev/fpga0/event6”, R);

  //polling on event4 and event6

  struct pollfd fds[] = {
      { fd4, POLLIN | POLLERR },
      { fd6, POLLIN | POLLERR }
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



** Q: How can i toggle an interrupt from within the CL ? **

Toggling of a user interrupts on the CL<=>Shell interface will generate an MSIX that gets translated to an event in linux userspace that an application can poll() on. Follow https://github.com/aws/aws-fpga/master/blob/hdl/docs/AWS_Shell_Interface_Specification.md) for details of the hardware interface



** Q: How do I stop events ? **

If the developers want to stop all the interrupts, he/she should disable the toggling of interrupt pins at the CL side (implementation specific)



** Q: How can i mask an interrupt/event ?**

There are three options:
i) An application can stop calling poll() on the event file-descriptor. The interrupt may still toggle and the kernel edma driver will get invoked by the the application in linux userspace will not see it.

ii) By calling close() for all file-descriptors associated with the specification interrupt/event, the edma driver will mask the interrupt

iii) Control the interrupt request signals at the interrupt between the CL and Shell.



**Q: Where are the cause and mask registers for the user-defined interrupts?**

The cause the mask bits, if exisit, will be part of the CL and are implementation specific. The example(s) given in this file, and the EDMA driver provides a robust way to translate an interrupts request on the CL to Shell interface to Linux kernel and userspace. It should be consider as message/event transfer mechanism.



## How count how many interrupts/events happened ?

  `cat /proc/interrupts`   and look for fpgaX_eventY for how many interrupts came from the CL via the corresponding MSI-X.
  `cat /TBD` will show how many times the userspace application called poll().



**Q: Could I miss an interrupt?**

Yes, that could happen: 
i) if the EDMA driver is not installed
ii) if the interrupt was delivered to Linux while the corresponding file-descriptor was not open by any process.
[TBD]



**Q: If I send multiple interupt request, will I need to poll() multiple times?**

It all depends on the timing when the interrupt request was sent and when the poll() is called.

EDMA implementation keeps a state per interrupt if it was asserted from the last time a poll() was called.  If the same interrupt is sent by the CL multiple time before the poll() is called, the next call to the poll() will just indicate that there was one or more interrupts, but it does not provide the interrupt count, and it does not keep a queue.



**Q: Which MSI-X entries are used for the user-defined interrupts ?**

The EDMA linux kernel driver will map the CL user defined interrupts to MSIX entries 16 to 31, which will consequently be mapped to /dev/fpgaX/event0 through 15.  All this is handled by the EDMA driver and user intervention is not required.



**Q: What if i want to built an in-kernel interrupt service routine for some of the user-defined interrupts?** 

A reference in-kernel driver interrupt handler is provider for user modification in [TBD] directory.
