#include <linux/module.h>
#include <linux/vermagic.h>
#include <linux/compiler.h>

MODULE_INFO(vermagic, VERMAGIC_STRING);

__visible struct module __this_module
__attribute__((section(".gnu.linkonce.this_module"))) = {
	.name = KBUILD_MODNAME,
	.init = init_module,
#ifdef CONFIG_MODULE_UNLOAD
	.exit = cleanup_module,
#endif
	.arch = MODULE_ARCH_INIT,
};

static const struct modversion_info ____versions[]
__used
__attribute__((section("__versions"))) = {
	{ 0xbc884195, __VMLINUX_SYMBOL_STR(module_layout) },
	{ 0x2d3385d3, __VMLINUX_SYMBOL_STR(system_wq) },
	{ 0x394a7d34, __VMLINUX_SYMBOL_STR(device_remove_file) },
	{ 0x9bfe1b60, __VMLINUX_SYMBOL_STR(cdev_del) },
	{ 0xaa28a96, __VMLINUX_SYMBOL_STR(kmalloc_caches) },
	{ 0x885f5151, __VMLINUX_SYMBOL_STR(pci_bus_read_config_byte) },
	{ 0xd2b09ce5, __VMLINUX_SYMBOL_STR(__kmalloc) },
	{ 0x5e6b55aa, __VMLINUX_SYMBOL_STR(cdev_init) },
	{ 0xf9a482f9, __VMLINUX_SYMBOL_STR(msleep) },
	{ 0xc897c382, __VMLINUX_SYMBOL_STR(sg_init_table) },
	{ 0x6bf1c17f, __VMLINUX_SYMBOL_STR(pv_lock_ops) },
	{ 0xb44d50bf, __VMLINUX_SYMBOL_STR(pcim_enable_device) },
	{ 0x33134013, __VMLINUX_SYMBOL_STR(param_ops_int) },
	{ 0xa90ac519, __VMLINUX_SYMBOL_STR(pci_disable_device) },
	{ 0xa8ebb0f5, __VMLINUX_SYMBOL_STR(pci_disable_msix) },
	{ 0x7a44e88e, __VMLINUX_SYMBOL_STR(device_destroy) },
	{ 0x3fec048f, __VMLINUX_SYMBOL_STR(sg_next) },
	{ 0x4150a873, __VMLINUX_SYMBOL_STR(pci_release_regions) },
	{ 0x54bd31b, __VMLINUX_SYMBOL_STR(mutex_unlock) },
	{ 0x7485e15e, __VMLINUX_SYMBOL_STR(unregister_chrdev_region) },
	{ 0x999e8297, __VMLINUX_SYMBOL_STR(vfree) },
	{ 0x7a2af7b4, __VMLINUX_SYMBOL_STR(cpu_number) },
	{ 0x91715312, __VMLINUX_SYMBOL_STR(sprintf) },
	{ 0xd8bb8c0b, __VMLINUX_SYMBOL_STR(kthread_create_on_node) },
	{ 0x9e88526, __VMLINUX_SYMBOL_STR(__init_waitqueue_head) },
	{ 0x4f8b5ddb, __VMLINUX_SYMBOL_STR(_copy_to_user) },
	{ 0x5c21b4f8, __VMLINUX_SYMBOL_STR(pci_set_master) },
	{ 0x33407b14, __VMLINUX_SYMBOL_STR(pci_enable_msix) },
	{ 0xdae114ba, __VMLINUX_SYMBOL_STR(pci_iounmap) },
	{ 0x5f9d0dce, __VMLINUX_SYMBOL_STR(dev_err) },
	{ 0x1916e38c, __VMLINUX_SYMBOL_STR(_raw_spin_unlock_irqrestore) },
	{ 0x90f4ac56, __VMLINUX_SYMBOL_STR(current_task) },
	{ 0x27e1a049, __VMLINUX_SYMBOL_STR(printk) },
	{ 0x73bd155b, __VMLINUX_SYMBOL_STR(kthread_stop) },
	{ 0x17947ade, __VMLINUX_SYMBOL_STR(class_unregister) },
	{ 0xa1c76e0a, __VMLINUX_SYMBOL_STR(_cond_resched) },
	{ 0x16305289, __VMLINUX_SYMBOL_STR(warn_slowpath_null) },
	{ 0xcd2912a8, __VMLINUX_SYMBOL_STR(mutex_lock) },
	{ 0xfd9aea16, __VMLINUX_SYMBOL_STR(device_create) },
	{ 0xc2cdbf1, __VMLINUX_SYMBOL_STR(synchronize_sched) },
	{ 0x2072ee9b, __VMLINUX_SYMBOL_STR(request_threaded_irq) },
	{ 0x952664c5, __VMLINUX_SYMBOL_STR(do_exit) },
	{ 0x21305b17, __VMLINUX_SYMBOL_STR(pci_find_capability) },
	{ 0x8cb1b0b6, __VMLINUX_SYMBOL_STR(device_create_file) },
	{ 0x96a8201, __VMLINUX_SYMBOL_STR(cdev_add) },
	{ 0x9933ea4e, __VMLINUX_SYMBOL_STR(arch_dma_alloc_attrs) },
	{ 0x163b2f43, __VMLINUX_SYMBOL_STR(_dev_info) },
	{ 0x40a9b349, __VMLINUX_SYMBOL_STR(vzalloc) },
	{ 0x78764f4e, __VMLINUX_SYMBOL_STR(pv_irq_ops) },
	{ 0x12a38747, __VMLINUX_SYMBOL_STR(usleep_range) },
	{ 0x1000e51, __VMLINUX_SYMBOL_STR(schedule) },
	{ 0xd62c833f, __VMLINUX_SYMBOL_STR(schedule_timeout) },
	{ 0x8daa027c, __VMLINUX_SYMBOL_STR(wake_up_process) },
	{ 0xbdfb6dbb, __VMLINUX_SYMBOL_STR(__fentry__) },
	{ 0x251ff614, __VMLINUX_SYMBOL_STR(pci_enable_msi_range) },
	{ 0x4e453bad, __VMLINUX_SYMBOL_STR(pci_unregister_driver) },
	{ 0x6c662899, __VMLINUX_SYMBOL_STR(kmem_cache_alloc_trace) },
	{ 0xe259ae9e, __VMLINUX_SYMBOL_STR(_raw_spin_lock) },
	{ 0x3d13352, __VMLINUX_SYMBOL_STR(__dynamic_dev_dbg) },
	{ 0x680ec266, __VMLINUX_SYMBOL_STR(_raw_spin_lock_irqsave) },
	{ 0xa6bbd805, __VMLINUX_SYMBOL_STR(__wake_up) },
	{ 0xb3f7646e, __VMLINUX_SYMBOL_STR(kthread_should_stop) },
	{ 0x2207a57f, __VMLINUX_SYMBOL_STR(prepare_to_wait_event) },
	{ 0x37a0cba, __VMLINUX_SYMBOL_STR(kfree) },
	{ 0x96c6cf11, __VMLINUX_SYMBOL_STR(pci_request_regions) },
	{ 0x32e18640, __VMLINUX_SYMBOL_STR(pci_disable_msi) },
	{ 0x4d3ce8ca, __VMLINUX_SYMBOL_STR(dma_supported) },
	{ 0x901b8b35, __VMLINUX_SYMBOL_STR(__pci_register_driver) },
	{ 0xae55a18c, __VMLINUX_SYMBOL_STR(class_destroy) },
	{ 0xf08242c2, __VMLINUX_SYMBOL_STR(finish_wait) },
	{ 0x2e0d2f7f, __VMLINUX_SYMBOL_STR(queue_work_on) },
	{ 0x41d161b9, __VMLINUX_SYMBOL_STR(pci_iomap) },
	{ 0x7f02188f, __VMLINUX_SYMBOL_STR(__msecs_to_jiffies) },
	{ 0x436c2179, __VMLINUX_SYMBOL_STR(iowrite32) },
	{ 0xb7e1097a, __VMLINUX_SYMBOL_STR(pci_enable_device) },
	{ 0x4f6b400b, __VMLINUX_SYMBOL_STR(_copy_from_user) },
	{ 0xc3cdd24b, __VMLINUX_SYMBOL_STR(__class_create) },
	{ 0xc6075568, __VMLINUX_SYMBOL_STR(dma_ops) },
	{ 0x29537c9e, __VMLINUX_SYMBOL_STR(alloc_chrdev_region) },
	{ 0xe484e35f, __VMLINUX_SYMBOL_STR(ioread32) },
	{ 0xf20dabd8, __VMLINUX_SYMBOL_STR(free_irq) },
	{ 0x8bb93c2b, __VMLINUX_SYMBOL_STR(pci_save_state) },
};

static const char __module_depends[]
__used
__attribute__((section(".modinfo"))) =
"depends=";

MODULE_ALIAS("pci:v00001D0Fd00001042sv*sd*bc*sc*i*");

MODULE_INFO(srcversion, "8A9620BA581CFC9DE2BEC3A");
