import argparse
import sys


class KeyValAction(argparse.Action):
    def __call__(self, parser, namespace, value, option_string=None):
        fragments = value.split(':')
        if len(fragments) != 2:
            raise ValueError(f'The value {value} does not have the expected form <key>:<value>')
        getattr(namespace, self.dest).append(tuple(fragments))


parser = argparse.ArgumentParser()
parser.add_argument('-s', dest='subsitutions', type=str, help='key:value to expand', action=KeyValAction, default=[])
args = parser.parse_args()


formula_text = sys.stdin.read()

for key, value in args.subsitutions:
    key = f'${{{key}}}'
    formula_text = formula_text.replace(key, value)

print(formula_text)
