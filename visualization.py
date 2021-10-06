from graphviz import Digraph
from typing import Callable, Dict, Tuple, List, Union, Set
from dataclasses import dataclass


def compute_html_label_for_symbols(variable_names: List[str], symbols: List[Tuple[int, ...]]):
    label = '<<TABLE BORDER="0" SIDES="LR" CELLPADDING="1" CELLSPACING="0">'

    table_row_count = len(symbols[0])
    table_column_count = len(symbols)

    for row in range(table_row_count):
        label += '<TR>'
        is_first_column = True
        label += f'<TD BORDER="0" BGCOLOR="gray">{variable_names[row]}:</TD>'
        for column in range(table_column_count):
            if not is_first_column:
                sides = "L"
                border = "1"
            else:
                sides = ""
                border = "0"

            label += f'<TD BORDER="{border}" sides="{sides}">'
            label += f'{symbols[column][row]}'
            label += '</TD>'

            is_first_column = False
        label += '</TR>'

    label += '</TABLE>>'
    return label


def convert_automaton_to_graphviz(nfa,
                                  automaton_label: str = 'No label provided.',
                                  node_naming_fn: Callable[[int], str] = None):

    raise RuntimeError('This is deprecated!')
    graph = Digraph('automaton', strict=True, graph_attr={'rankdir': 'LR', 'ranksep': '1'})

    if not node_naming_fn:
        def naming_fn(index: int):
            return str(index)
        node_naming_fn = naming_fn

    state_node_names: Dict[int, str] = {}

    for index, state in enumerate(nfa.states):
        node_name = node_naming_fn(index)
        if state in nfa.final_states:
            graph.node(node_name, str(state), shape='doublecircle')
        else:
            graph.node(node_name, str(state))
        state_node_names[state] = node_name

    for index, state in enumerate(nfa.initial_states):
        initial_point_name = f'{state}@Start'
        graph.node(initial_point_name, shape='point')
        graph.edge(initial_point_name, state_node_names[state])

    for origin in nfa.transition_fn:
        origin_node_name = state_node_names[origin]
        for destination in nfa.transition_fn[origin]:
            destination_node_name = state_node_names[destination]
            transition_symbols = nfa.transition_fn[origin][destination]
            graph.edge(
                origin_node_name,
                destination_node_name,
                label=compute_html_label_for_symbols(
                    nfa.alphabet.variable_names,
                    list(transition_symbols),
                    )
            )

    graph.attr(label=f'<<FONT POINT-SIZE="27">{automaton_label}</FONT>>')

    return graph


IntOrStr = Union[str, int]
TransitionSymbols = Tuple[Tuple[IntOrStr, ...]]
Transition = Tuple[IntOrStr, TransitionSymbols, IntOrStr]


@dataclass
class AutomatonVisRepresentation:
    '''A class describing the visual representation of the automaton.'''
    initial_states: Set[IntOrStr]
    final_states:   Set[IntOrStr]
    states:         Set[IntOrStr]
    transitions:    List[Transition]
    variable_names: Tuple[str, ...]

    def into_graphviz(self) -> Digraph:
        '''Transforms the stored automaton represenation into graphviz (/dot).'''
        graph = Digraph('automaton',
                        strict=True,
                        graph_attr={
                            'rankdir': 'LR',
                            'ranksep': '1'})

        for state in self.states:
            if state in self.final_states:
                graph.node(str(state), str(state), shape='doublecircle')
            else:
                graph.node(str(state), str(state))

        for state in self.initial_states:
            initial_point_name = f'{state}@Start'
            graph.node(initial_point_name, shape='point')
            graph.edge(initial_point_name, str(state))

        for origin_state, transition_symbols, dest_state in self.transitions:
            graph.edge(
                str(origin_state),
                str(dest_state),
                label=compute_html_label_for_symbols(
                    self.variable_names,
                    list(transition_symbols),
                    )
            )
        return graph

    def compress_symbols(self):
        '''Peforms transition sets compression using plain BDDs.'''
        from dd.autoref import BDD
        manager = BDD()

        variables = [chr(ord('a') + i) for i in range(len(self.variable_names))]

        manager.declare(*tuple(variables))
        self.variable_names = variables

        compressed_transitions: List[Transition] = []

        for origin_state, transition_symbols, destination_state in self.transitions:
            bdd = manager.add_expr('False')
            for transition_symbol in transition_symbols:
                symbol_literals = []
                for i, bit in enumerate(transition_symbol):
                    if bit == 0:
                        symbol_literals.append(f'!{self.variable_names[i]}')
                    elif bit == 1:
                        symbol_literals.append(f'{self.variable_names[i]}')
                if symbol_literals:
                    clause = ' & '.join(symbol_literals)
                    bdd |= manager.add_expr(clause)

            manager.collect_garbage()
            # All symbols leading from A to B are in the BDD, convert it back
            compressed_symbols = []
            for model in manager.pick_iter(bdd, []):
                symbol = []

                # Model is a dictionary of the support variables of our bdd to
                # their assignment (some vars - do not care bits) might be
                # missing
                for v in self.variable_names:
                    if v in model:
                        symbol.append(int(model[v]))
                    else:
                        symbol.append('*')

                compressed_symbols.append(tuple(symbol))

            # It might be the case that between two states, every single one of
            # the alphabet symbols is present in which case there are no
            # support variables and therefore no models (every assignment is a
            # model) -->> compressed symbols is empty.
            if not compressed_symbols:
                universal_symbol = tuple(['*'] * len(self.variable_names))
                compressed_symbols.append(universal_symbol)

            compressed_transitions.append((origin_state, compressed_symbols, destination_state))

        self.transitions = compressed_transitions
        return self
