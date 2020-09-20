import logging

logger = logging.getLogger('pressburger-solver')
logger.setLevel(logging.DEBUG)

console_handler = logging.StreamHandler()
console_handler.setLevel(logging.DEBUG)

formatter = logging.Formatter('[%(asctime)s](%(levelname)s)- [%(funcName)s]: %(message)s', datefmt='%Y/%m/%d %H:%M:%S')

console_handler.setFormatter(formatter)
logger.addHandler(console_handler)
