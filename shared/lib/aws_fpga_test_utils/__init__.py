
import logging

def configure_logger(name):
    logger = logging.getLogger(name)
    logger_console_handler = logging.StreamHandler()
    logger_formatter = logging.Formatter('%(levelname)s:%(asctime)s: %(message)s')
    logger_console_handler.setFormatter(logger_formatter)
    logger.addHandler(logger_console_handler)
    logger.setLevel(logging.INFO)
    return logger