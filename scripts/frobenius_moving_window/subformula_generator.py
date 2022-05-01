"""
Generates the formula (where w1, w2 are parameters):
    (forall ((p Int))
        (exists ((x1 Int) (x2 Int))
            (= p (+ (* x1 w1) (* x1 w2)))
        )
    )
"""
import argparse

def mk_arg_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument('w1', type=int, help='The first formula parameter.')
    parser.add_argument('w2', type=int, help='The second formula parameter.')
    return parser

def generate_formula(w1: int, w2: int) -> str:
    """
    Generate the formula. 
    """
    
    header = '(set-logic LIA)\n'
    formula_template = ('(assert \n'
                        '    (forall ((z Int)) \n'
                        '        (exists ((x Int) (y Int))\n'
                        '            (= z (+ (* x {w1}) (* y {w2})))\n'
                        '        )\n'
                        '    )\n'
                        ')\n')
    footer = ('(check-sat)\n'
              '(exit)')

    return header + formula_template.format(w1=w1, w2=w2) + footer


if __name__ == '__main__':
    args = mk_arg_parser().parse_args()
    print(generate_formula(args.w1, args.w2))
