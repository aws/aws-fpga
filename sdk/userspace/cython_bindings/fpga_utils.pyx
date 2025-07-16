# fpga_utils.pyx
from fpga_mgmt cimport fpga_mgmt_strerror
from logging import getLogger

logger = getLogger(__name__)

def check_return_code(ret: int, check: str, slot_id: int) -> None:
    slot_str = "N/A" if slot_id == -1 else str(slot_id)
    if ret != 0:
        error_message = fpga_mgmt_strerror(ret).decode('utf-8')
        raise RuntimeError(f"Failed to {check} on slot: {slot_str}, error code: {ret}: {error_message}")
    logger.info(f"Succeeded to {check} on slot: {slot_str}")
