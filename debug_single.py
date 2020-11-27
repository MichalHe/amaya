import sys
import parse
import visualization
import os
import argparse
import functools

OPERATION_NAMES = {
    parse.ParsingOperation.BUILD_NFA_FROM_INEQ: 'build_from_ineq',
    parse.ParsingOperation.BUILD_NFA_FROM_SHARP_INEQ: 'build_from_sharp_ineq',
    parse.ParsingOperation.BUILD_NFA_FROM_EQ: 'build_from_sharp_ineq',
    parse.ParsingOperation.NFA_UNION: 'union',
    parse.ParsingOperation.NFA_PROJECTION: 'projection',
    parse.ParsingOperation.NFA_COMPLEMENT: 'complement',
    parse.ParsingOperation.NFA_DETERMINIZE: 'determinize',
    parse.ParsingOperation.NFA_INTERSECT: 'intersect',
}

arg_parser = argparse.ArgumentParser()
arg_parser.add_argument('input_file',
                        help='File containing the SMT2 source for automaton under debug.',
                        type=str
                        )

arg_parser.add_argument('-d',
                        '--destination',
                        help='Destination folder for the output graphviz automatons',
                        dest='destination_dir',
                        type=str,
                        default='/tmp/amaya_debug'
                        )

args = arg_parser.parse_args()


if not os.path.exists(args.input_file):
    print(f'Given input file {args.input_file} does not exists.', file=sys.stderr)
    sys.exit(1)

if not os.path.exists(args.destination_dir):
    print(f'Destination directory {args.destination_dir} does not exitsts, creating.')
    os.mkdir(args.destination_dir)

# Add each produced automaton unique id
automaton_cnt = 0


def nfa_emitted_handle(destination, nfa, parse_op):
    global automaton_cnt
    automaton_graphviz = visualization.convert_automaton_to_graphviz(nfa)
    operation_name = OPERATION_NAMES[parse_op]
    output_path = os.path.join(destination, f'debug_{automaton_cnt}_{operation_name}.gv')
    with open(output_path, 'w') as output_file:
        output_file.write(str(automaton_graphviz))
    automaton_cnt += 1


with open(args.input_file) as input_file:
    source_text = input_file.read()
    debug_handle = functools.partial(nfa_emitted_handle, args.destination_dir)
    parse.check_result_matches(source_text, emit_introspect=debug_handle)
