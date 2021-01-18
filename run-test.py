from parse import (
    check_result_matches
)
from log import logger
import os
import re
import logging
import argparse as ap
import timeit
import functools
import csv

logger.setLevel(logging.CRITICAL)


arg_parser = ap.ArgumentParser()
arg_parser.add_argument(
    '-t',
    '--time-it',
    dest='perform_timing',
    default=False,
    action='store_true'
)

arg_parser.add_argument(
    '-v',
    '--verbose',
    dest='verbose',
    default=False,
    action='store_true'
)

args = arg_parser.parse_args()

if args.verbose:
    logger.setLevel(logging.INFO)


def check_file(test_filepath, timings=None):
    with open(test_filepath, 'r') as smt_file:
        smt_text = smt_file.read()

        if timings is not None:
            runtime = timeit.timeit(functools.partial(check_result_matches, smt_text), number=1)
            timings[test_filepath] = runtime

        return check_result_matches(smt_text)


TEST_ROOT = './smt-files/tptp'
EXTENSION_REGEX = re.compile(r'.*\.smt2$')

root_files = os.listdir(TEST_ROOT)

test_filepaths = []
wrong_answers = []
tests_cnt = 0

timings = None
if args.perform_timing:
    timings = {}


for root_file in root_files:
    if EXTENSION_REGEX.search(root_file):
        test_path = os.path.join(TEST_ROOT, root_file)
        test_filepaths.append(test_path)

        logger.info(f'Running {test_path}')
        check = check_file(test_path, timings=timings)
        if not check:
            wrong_answers.append(root_file)

        tests_cnt += 1

if args.perform_timing:
    with open('amaya_timings.csv', 'w') as output_file:
        csv_writer = csv.writer(output_file)
        fields = ['Test name', 'Amaya']
        csv_writer.writerow(fields)

        for test_path, runtime in timings.items():
            testname = os.path.basename(test_path)
            csv_writer.writerow([testname, runtime])


print(f'Incorrect {len(wrong_answers)}/{tests_cnt}')

print('Wrong answers:')
for wrong_answer in wrong_answers:
    print(wrong_answer)
