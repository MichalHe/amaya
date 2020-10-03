from inequations import build_nfa_from_inequality, extract_inquality
from visualization import convert_automaton_to_graphviz
from argparse import ArgumentParser
import parse
import sys
import utils

arg_parser = ArgumentParser()
arg_parser.add_argument('-i',
                        '--input-file',
                        help='Read from file instead of stdin',
                        dest='file_input',
                        type=str,
                        default=None)

args = arg_parser.parse_args()


def export_dot_from_stmlibsrc(smtlib_src: str) -> str:
    tokens = parse.lex(smtlib_src)
    expr_tree = parse.build_syntax_tree(tokens)

    asserts = parse.filter_asserts(expr_tree)

    # FIXME: Get other types of inequalities too
    formula = parse.get_formula(asserts[0])
    ineq_tree = utils.search_tree(formula, '<=')

    ineq = extract_inquality(ineq_tree)

    nfa = build_nfa_from_inequality(ineq)

    return convert_automaton_to_graphviz(nfa)


if args.file_input:
    with open(args.file_input) as input_file:
        smtlib_src = input_file.read()
else:
    smtlib_src = sys.stdin.read()

print(export_dot_from_stmlibsrc(smtlib_src))
