from automatons import NFA
from transitions import iter_transition_fn
from utils import number_to_bit_tuple

# VTF format example:
# @NFA-BDD          # NFAs with transitions in BDD
# %Symbol-Vars 8    # number of Boolean variables in the alphabet (required)
# %Initial q1 q2
# %Final q2

# q1 000x11x1 q2    # the format is <source> <symbol> <target>
# q1 01101111 q3    # 'x' in the binary vector denote don't care values
# q3 xxxxxxxx q1    # the length needs to match the value in '%Symbol-Vars'


def iter_alphabet_symbol(symbol):
    # Input: Symbol (*, 0, 1, *)
    if len(symbol) == 0:
        return

    # Collect the positions of the dont-care bits
    dont_care_indices = []
    for i, bit in enumerate(symbol):
        if bit == '*':
            dont_care_indices.append(i)

    if len(dont_care_indices) == 0:
        yield tuple(symbol)
        return

    g_symbol = list(symbol)

    for k in range(2**len(dont_care_indices)):
        # evaluate the dont-care bits
        dont_care_indices_values = number_to_bit_tuple(k, tuple_size=len(dont_care_indices))

        # Shuffle the don't care bits values into the generated symbol
        for i, dc_bit_value in enumerate(dont_care_indices_values):
            dc_bit_index = dont_care_indices[i]
            g_symbol[dc_bit_index] = dc_bit_value

        yield tuple(g_symbol)


def convert_automaton_to_vtf(automaton: NFA) -> str:
    alphabet_size = len(automaton.alphabet.variable_names)
    initial_state = tuple(automaton.initial_states)[0]  # There is only 1 state
    final_states = ' '.join(map(str, automaton.final_states))
    states = ' '.join(map(str, automaton.states))

    vtf = ''
    vtf += '@NFA\n'
    vtf += f'%States {states}\n'
    vtf += f'%Initial {initial_state}\n'
    vtf += f'%Final {final_states}\n'

    # Just to be sure, include metadata
    vtf += f'%Symbol-Vars {alphabet_size}\n'
    vtf += '\n'

    # Add automaton transition function
    for transition in iter_transition_fn(automaton.transition_fn):
        source, symbol, destination = transition

        # Expand the symbol transition
        for ex_symbol in iter_alphabet_symbol(symbol):
            ex_symbol_str = ''.join(map(str, ex_symbol))
            vtf += f'{source} {ex_symbol_str} {destination}\n'

    return vtf


def convert_automaton_to_rabbit(nfa: NFA) -> str:
    # Rabbit does not support '-' in the BA format, rename states
    _, renamed_nfa = nfa.rename_states()

    initial_state = tuple(renamed_nfa.initial_states)[0]

    rabbit_fmt = ''
    rabbit_fmt += f'[{initial_state}]\n'

    for transition in iter_transition_fn(renamed_nfa.transition_fn):
        src, symbol, dest = transition
        # We need to expand the symbol because it might be a symbolic one
        for expanded_sym in iter_alphabet_symbol(symbol):
            symbol_str = ''.join(map(str, expanded_sym))
            rabbit_fmt += f'{symbol_str},[{src}]->[{dest}]\n'

    for i, fstate in enumerate(renamed_nfa.final_states):
        # This is not necessary, but the empty line at the end is not pretty
        if i < len(nfa.final_states) - 1:
            rabbit_fmt += f'[{fstate}]\n'
        else:
            rabbit_fmt += f'[{fstate}]'

    return rabbit_fmt
