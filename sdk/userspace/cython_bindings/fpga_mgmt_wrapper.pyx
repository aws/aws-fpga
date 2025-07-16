# Cython Code File for FPGA Management library

from fpga_mgmt cimport *
from libc.stdint cimport uint16_t, uint32_t
import logging
from fpga_utils import check_return_code
from typing import Dict, List, Any

class FpgaMgmt:
    def __init__(self) -> None:
        init_status = fpga_mgmt_init()
        check_return_code(init_status, "initialize FPGA Management Library", -1)

    def __del__(self) -> None:
        logging.info("Closing FPGA Management Library")
        fpga_mgmt_close()

    def load_local_image(self, slot_id : int, afi_id: str) -> Dict[str, Any]:
        cdef bytes afi_id_bytes = afi_id.encode('utf-8')
        ret = fpga_mgmt_load_local_image(slot_id, afi_id_bytes)
        check_return_code(ret, "load AFI", slot_id)
        return FpgaMgmt.describe_local_image(self, slot_id, 1<<1)

    def clear_local_image(self, slot_id: int) -> Dict[str, Any]:
        ret = fpga_mgmt_clear_local_image(slot_id)
        check_return_code(ret, "clear image on FPGA", slot_id)
        return FpgaMgmt.describe_local_image(self, slot_id, 1<<1)

    @staticmethod
    def process_cached_agfis(result: dict) -> List[str]:
        formatted_agfis = []
        for agfi_value in result['metrics']['cached_agfis']:
            if agfi_value == 0:
                formatted_agfis.append('0')
            else:
                formatted_agfis.append('agfi-' + hex(agfi_value)[2:])
        return formatted_agfis

    def describe_local_image(self, slot_id: int, flags: uint32_t) -> Dict[str, Any]:
        cdef fpga_mgmt_image_info info

        ret = fpga_mgmt_describe_local_image(slot_id, &info, flags)
        check_return_code(ret, "describe local image", slot_id)

        result = {
            'status': FpgaMgmt.get_status_name(info.status),
            'status_q': info.status_q,
            'slot_id': info.slot_id,
            'afi_id': info.ids,
            'spec': info.spec,
            'sh_version': info.sh_version,
            'metrics': info.metrics.f2_metrics,
        }

        result['metrics']['cached_agfis'] = FpgaMgmt.process_cached_agfis(result)
        return result

    @staticmethod
    def strerror(error: int) -> str:
        val = fpga_mgmt_strerror(error)
        return val.decode('utf-8')

    @staticmethod
    def strerror_long(err: int) -> str:
        val = fpga_mgmt_strerror_long(err)
        return val.decode('utf-8')

    @staticmethod
    def get_status_name(status: int) -> str:
        return fpga_mgmt_get_status_name(status).decode('utf-8')

    def get_status(self, slot_id: int) -> Dict[str, Any]:
        cdef int status = 0
        cdef int status_q = 0
        ret = fpga_mgmt_get_status(slot_id, &status, &status_q)
        check_return_code(ret, "get FPGA status", slot_id)
        return {'status': status, 'status_q': status_q, 'return_code': ret}

    def set_cmd_timeout(self, value: uint32_t) -> None:
        fpga_mgmt_set_cmd_timeout(value)

    def set_cmd_delay_msec(self, value: uint32_t) -> None:
        fpga_mgmt_set_cmd_delay_msec(value)

    def get_vLED_status(self, slot_id: int) -> uint16_t:
        cdef uint16_t status
        ret = fpga_mgmt_get_vLED_status(slot_id, &status)
        check_return_code(ret, "get vLED status", slot_id)
        return status

    def set_vDIP(self, slot_id: int, value: uint16_t) -> None:
        ret = fpga_mgmt_set_vDIP(slot_id, value)
        check_return_code(ret, "set vDIP status", slot_id)

    def get_vDIP_status(self, slot_id: int) -> uint16_t:
        cdef uint16_t value
        ret = fpga_mgmt_get_vDIP_status(slot_id, &value)
        check_return_code(ret, "get vDIP status", slot_id)
        return value

    def clear_local_image_sync(self, slot_id: int, timeout: uint32_t, delay_msec: uint32_t) -> Dict[str, Any]:
        cdef fpga_mgmt_image_info info
        ret = fpga_mgmt_clear_local_image_sync(slot_id, timeout, delay_msec, &info);
        check_return_code(ret, "clear local image sync", slot_id)
        return FpgaMgmt.describe_local_image(self, slot_id, 1<<1)

    def load_local_image_flags(self, slot_id: int, afi_id: str, flags: uint32_t) -> Dict[str, Any]:
        cdef bytes afi_id_bytes = afi_id.encode('utf-8')
        ret = fpga_mgmt_load_local_image_flags( slot_id, afi_id_bytes,  flags);
        check_return_code(ret, "load AFI flags", slot_id)
        return FpgaMgmt.describe_local_image(self, slot_id, 1<<1)

    def load_local_image_sync_flags(self, slot_id: int, afi_id: str, flags: uint32_t, timeout: uint32_t, delay_msec: uint32_t) -> Dict[str, Any]:
        cdef fpga_mgmt_image_info info
        cdef bytes afi_id_bytes = afi_id.encode('utf-8')
        ret = fpga_mgmt_load_local_image_sync_flags(slot_id, afi_id_bytes, flags, timeout, delay_msec, &info)
        check_return_code(ret, "load AFI sync flags", slot_id)
        return FpgaMgmt.describe_local_image(self, slot_id, 1<<1)

