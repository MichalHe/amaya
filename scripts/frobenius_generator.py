#!/usr/bin/python3
import sys


def weighted_sum(coefs, _vars):
    return '(+ {0})'.format(' '.join(f'(* {coef} {var})' for coef, var in zip(coefs, _vars)))


def conjunction(*args):
    return '(and {0})'.format(' '.join(args))


def not_eq(left, right):
    return f'(not (= {left} {right}))'


def forall(vars, formula):
    binding = ' '.join([f'({var} Int)' for var in vars])
    return f'(forall ({binding}) {formula})'


def implies(left, right):
    return f'(=> {left} {right})'


def gen_is_frobenius_candidate(var, coeficients, exist_var_prefix='x'):
    binding_vars = [f'{exist_var_prefix}{i}' for i, _ in enumerate(coeficients)]
    all_binding_vars_gte_zero = [f'(<= 0 {var})' for var in binding_vars]

    return forall(
        binding_vars, 
        implies(
            conjunction(*all_binding_vars_gte_zero),
            not_eq(weighted_sum(binding_vars, coeficients), var)
        ))


def ineq(left, right):
    return f'(<= {left} {right})'


def smt_preamble(var):
    preable = [
        '(set-logic LIA)',
        f'(declare-fun {var} () Int)',
        ''
    ]    
    return '\n'.join(preable)


def smt_fin():
    fin = [
        '(check-sat)',
        '(exit)',
        ''
    ]
    return '\n'.join(fin)

def _assert(formula):
    return f'(assert {formula})'


def generate_frobenius_number_formula(coefs):
    formula = conjunction(
        gen_is_frobenius_candidate('P', coefs), 
        forall(
            ['R'], 
            implies(
                gen_is_frobenius_candidate('R', coefs),
                ineq('R', 'P'))))

    return smt_preamble('P') + _assert(formula) + '\n' + smt_fin()


def print_usage_and_exit():
    print('Usage: ./frobenius_generator.py coeficient1,coeficient2,coeficient3')
    sys.exit(1)


if len(sys.argv) != 2:
    print_usage_and_exit()

coef_strings = sys.argv[1].split(',')
coefs = []
for coef_str in coef_strings:
    try:
        coef = int(coef_str)
        if coef <= 0:
            print('Given coeficient is not an integer greater than zero.')
            print_usage_and_exit()
        coefs.append(coef)
    except ValueError:
            print('Given coeficient is not an integer.')
            print_usage_and_exit()


print(generate_frobenius_number_formula(coefs))
