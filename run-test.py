from parse import (
    check_result_matches
)
from log import logger
import os
import re
import logging

logger.setLevel(logging.CRITICAL)


def check_file(test_filepath):
    with open(test_filepath, 'r') as smt_file:
        smt_text = smt_file.read()
        return check_result_matches(smt_text)


TEST_ROOT = './smt-files/tptp'
EXTENSION_REGEX = re.compile(r'.*\.smt2$')

root_files = os.listdir(TEST_ROOT)

test_filepaths = []
wrong_answers = []
for root_file in root_files:
    if EXTENSION_REGEX.search(root_file):
        test_path = os.path.join(TEST_ROOT, root_file)
        test_filepaths.append(test_path)

        print(f'Running {test_path}')
        check = check_file(test_path)
        if not check:
            logger.setLevel(logging.INFO)
            check_file(test_path)
            wrong_answers.append(root_file)
        else:
            logger.setLevel(logging.CRITICAL)

print(f'Incorrect {len(wrong_answers)}/{len(root_files)}')

print('Wrong answers:')
for wrong_answer in wrong_answers:
    print(wrong_answer)
