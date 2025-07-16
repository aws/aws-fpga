import logging, json


def setup_logger() -> None:
    # Change logging level to logging.INFO for verbose Cython methods
    logging.basicConfig(
        level=logging.WARNING,
        format="%(asctime)s - %(levelname)s - %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )


def convert_info_to_json(info: dict) -> str:
    afi_id_decoded = info["afi_id"]["afi_id"].decode("utf-8")
    info["afi_id"]["afi_id"] = afi_id_decoded
    return json.dumps(info, indent=2)
