"""Shared helpers for the F2 workshop notebooks."""


def fmt_hex32(value: int) -> str:
    """Format an integer as a zero-padded 32-bit hex string.

    Args:
        value: Integer to format. Masked to 32 bits.

    Returns:
        str: Hex string in the form '0x00000000'.
    """
    return f"0x{value & 0xFFFFFFFF:08X}"


def poll_register(pci, handle, addr, mask, max_attempts=100):
    """Poll a register until (value & mask) is non-zero.

    Reads the register at `addr` up to `max_attempts` times. Returns as
    soon as the masked bits are set. On timeout, prints an error message
    and returns -1.

    Args:
        pci:          FpgaPCI instance (from fpga_pci_wrapper).
        handle:       PCI BAR handle returned by pci_attach().
        addr:         Register byte offset to poll.
        mask:         Bitmask to test against the register value.
        max_attempts: Maximum number of peek attempts (default 100).

    Returns:
        int: The register value when (value & mask) != 0, or -1 on timeout.
    """
    for _ in range(max_attempts):
        val = pci.pci_peek(handle, addr)
        if val & mask:
            return val
    else:
        print(f"❌ Timeout after {max_attempts} polls: register {fmt_hex32(addr)} & {fmt_hex32(mask)} never set")
        return -1


def print_fpga_info(info: dict) -> None:
    """Print a concise summary of an fpga_mgmt describe_local_image result.

    Extracts the most relevant fields from the full info dict returned by
    FpgaMgmt.describe_local_image() and related functions (load_local_image,
    clear_local_image, etc.). Metrics error counters are only shown if non-zero.

    Args:
        info: Dict returned by any FpgaMgmt function that calls describe_local_image.
    """
    # Core status
    print(f"  Slot:       {info.get('slot_id', '?')}")
    print(f"  Status:     {info.get('status', '?')}")
    status_q = info.get("status_q", 0)
    if status_q:
        print(f"  Status Q:   {status_q}")

    # AFI ID
    ids = info.get("afi_id", {})
    afi_id = ids.get("afi_id", b"").rstrip(b"\x00").decode("utf-8", errors="replace") if isinstance(ids, dict) else str(ids)
    if afi_id:
        print(f"  AFI ID:     {afi_id}")

    # Shell version
    sh_ver = info.get("sh_version", 0)
    if sh_ver:
        print(f"  Shell Ver:  0x{sh_ver:08X}")

    # Metrics — only non-zero error counters
    metrics = info.get("metrics", {})
    if not isinstance(metrics, dict):
        return

    error_fields = [
        ("pcim_range_error_count", "PCIM Range Errors"),
        ("pcim_axi_protocol_error_count", "PCIM AXI Protocol Errors"),
        ("dma_pcis_timeout_count", "DMA PCIS Timeouts"),
        ("ocl_slave_timeout_count", "OCL Slave Timeouts"),
        ("sda_slave_timeout_count", "SDA Slave Timeouts"),
        ("virtual_jtag_slave_timeout_count", "VJTAG Slave Timeouts"),
    ]

    errors_found = False
    for field, label in error_fields:
        val = metrics.get(field, 0)
        if val:
            if not errors_found:
                print("  Errors:")
                errors_found = True
            print(f"    {label}: {val}")

    if not errors_found:
        print("  Errors:     None")

    # Cached AGFIs (if any non-zero)
    cached = metrics.get("cached_agfis", [])
    non_zero = [a for a in cached if a != "0" and a != 0]
    if non_zero:
        print(f"  Cached AFIs: {', '.join(str(a) for a in non_zero)}")
