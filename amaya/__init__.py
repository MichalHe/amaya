import logging

logger = logging.getLogger('pressburger-solver')
logger.setLevel(logging.DEBUG)

console_handler = logging.StreamHandler()
console_handler.setLevel(logging.DEBUG)

formatter = logging.Formatter('[%(asctime)s](%(levelname)s): %(message)s', datefmt='%Y/%m/%d %H:%M:%S')

console_handler.setFormatter(formatter)
logger.addHandler(console_handler)

shard_logger = logging.getLogger('pressburger-solver-sharding')
shard_logger.setLevel(logging.DEBUG)
shard_logger.addHandler(console_handler)
