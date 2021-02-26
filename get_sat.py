import argparse
from log import logger
import logging
from parse import check_result_matches


ap = argparse.ArgumentParser()
ap.add_argument('file',
                help='File containing the SMT2 formula in question.')

args = ap.parse_args()

logger.setLevel(logging.DEBUG)

with open(args.file, 'r') as formula_file:
    src = formula_file.read()
    check_result_matches(src)
