from graphviz import Digraph
from automatons import NFA
from typing import Callable, Dict, Tuple, List


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


def convert_automaton_to_graphviz(nfa: NFA,
                                  automaton_label: str = '',
                                  node_naming_fn: Callable[[int], str] = None):
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
