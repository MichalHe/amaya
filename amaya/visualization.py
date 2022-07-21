from collections import (
    defaultdict
)
from dataclasses import (
    dataclass,
    field
)
from random import randint
from typing import (
    Any,
    Callable,
    Dict,
    Generator,
    Iterable,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)

from amaya.alphabet import (
    LSBF_AlphabetSymbol,
)
from amaya.ast_definitions import AST_Node
from amaya.relations_structures import Relation
from amaya.utils import (
    COLOR_PALETTE,
    find_sccs_kosaruju,
    get_color_palette_with_min_size,
    number_to_bit_tuple,
)

from graphviz import Digraph


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
    """A class describing the visual representation of the automaton."""
    initial_states: Set[IntOrStr]
    final_states:   Set[IntOrStr]
    states:         Set[IntOrStr]
    transitions:    List[Transition]
    variable_names: Tuple[str, ...]
    variable_ids:   Tuple[int, ...]
    state_labels:   Dict[int, Any] = field(default_factory=dict)

    def _compute_state_colors_by_sccs(self) -> Dict[int, Tuple[str, str]]:
        """
        Computes a dictionary mapping state to the color of the SCC they are in.

        SCCs of size 1 are ignored.
        """
        state_colors: Dict[int, Tuple[str, str]] = {}

        graph_edges = defaultdict(set)
        for source, dummy_symbols, destination in self.transitions:
            graph_edges[source].add(destination)

        # Ignore SCCs with only 1 node, they are not interesting
        sccs = [scc for scc in find_sccs_kosaruju(graph_edges) if len(scc) > 1]

        colors = get_color_palette_with_min_size(len(sccs))

        # Assign colors to states based on the SCC they are in
        for i, scc in enumerate(sccs):
            for state in scc:
                state_colors[state] = colors[i]
        return state_colors


    def into_graphviz(self, highlight_sccs: bool = False) -> Digraph:
        """Transforms the stored automaton represenation into graphviz (dot)."""
        graph = Digraph('automaton',
                        strict=True,
                        graph_attr={
                            'rankdir': 'LR',
                            'ranksep': '1'})

        # Compute the SCCs and assign colors accordingly
        state_colors: Dict[int, Tuple[str, str]] = self._compute_state_colors_by_sccs() if highlight_sccs else {}

        def gen_color_kwargs(state: int) -> Dict:
            if state in state_colors:
                state_color = state_colors[state]
                return {
                        'fillcolor': state_color[0],
                        'fontcolor': state_color[1],
                        'style': 'filled'
                }
            return {}


        for state in self.states:
            state_label = str(self.state_labels.get(state, state))
            shape = 'doublecircle' if state in self.final_states else 'circle'
            graph.node(state_label, state_label, shape=shape, **gen_color_kwargs(state))

        for state in self.initial_states:
            initial_point_name = f'{state}@Start'
            initial_state_label = str(self.state_labels.get(state, state))
            graph.node(initial_point_name, shape='point')
            graph.edge(initial_point_name, initial_state_label)

        for origin_state, transition_symbols, dest_state in self.transitions:
            origin_label = str(self.state_labels.get(origin_state, origin_state))
            dest_label = str(self.state_labels.get(dest_state, dest_state))
            edge_label = compute_html_label_for_symbols(self.variable_names, list(transition_symbols))
            graph.edge(origin_label,
                       dest_label,
                       label=edge_label)
        return graph

    def into_vtf(self, uncompress_symbols=False) -> str:
        """
        Converts the automaton representation to the VTF format.

        VTF format:
             https://github.com/ondrik/automata-benchmarks/blob/c554e59dab98ea1f985431ccaf6c142821717cfc/vtf/README.md
        """
        # VTF format example:
        # @NFA-BDD          # NFAs with transitions in BDD
        # %Symbol-Vars 8    # number of Boolean variables in the alphabet (required)
        # %Initial q1 q2
        # %Final q2

        # q1 000x11x1 q2    # the format is <source> <symbol> <target>
        # q1 01101111 q3    # 'x' in the binary vector denote don't care values
        # q3 xxxxxxxx q1    # the length needs to match the value in '%Symbol-Vars'

        initial_state = self.initial_states
        final_states = ' '.join(map(str, self.final_states))
        states = ' '.join(map(str, self.states))

        def join_list(seq: Iterable[IntOrStr]) -> str:
            return ' '.join(map(str, seq))

        vtf = '@NFA\n'
        vtf += '%States {0}\n'.format(join_list(self.states))
        vtf += '%Initial {0}\n'.format(join_list(self.initial_states))
        vtf += '%Final {0}\n'.format(join_list(self.final_states))

        # Just to be sure, include metadata about number of variables in the alphabet
        vtf += '%Symbol-Vars {0}\n'.format(len(self.variable_names))
        vtf += '\n'

        # Add automaton transition function
        for source, transition_symbols, destination in self.transitions:
            for compressed_symbol in transition_symbols:
                if uncompress_symbols:
                    for symbol in AutomatonVisRepresentation._uncompress_symbol(compressed_symbol):
                        vtf += '{0} {1} {2}\n'.format(source, ''.join(map(str, symbol)), destination)
                else:
                    vtf += '{0} {1} {2}\n'.format(
                            source,
                            ''.join(map(str, compressed_symbol)).replace('*', 'x'),
                            destination)


        return vtf

    @staticmethod
    def _uncompress_symbol(symbol: LSBF_AlphabetSymbol) -> Generator[Tuple[int, ...], None, None]:
        """Uncompress the given symbol yielding the symbolically represented symbols."""
        if not symbol:
            return

        dont_care_indices = tuple(i for i, bit in enumerate(symbol) if bit == '*')
        if not dont_care_indices:
            yield symbol
            return

        symbol_template = list(symbol)
        for k in range(2**len(dont_care_indices)):
            dont_care_bit_values = number_to_bit_tuple(k, tuple_size=len(dont_care_indices))
            for i, dont_care_bit_value in enumerate(dont_care_bit_values):
                dont_care_bit_index = dont_care_indices[i]
                symbol_template[dont_care_bit_index] = dont_care_bit_value
            yield tuple(symbol_template)

    def compress_symbols(self):
        """Peforms transition sets compression using plain BDDs."""
        from dd.autoref import BDD
        manager = BDD()

        bdd_unique_vars = [chr(ord('a') + i) for i in range(len(self.variable_names))]

        manager.declare(*tuple(bdd_unique_vars))

        compressed_transitions: List[Transition] = []

        for origin_state, transition_symbols, destination_state in self.transitions:
            bdd = manager.add_expr('False')
            for transition_symbol in transition_symbols:
                symbol_literals = []
                for i, bit in enumerate(transition_symbol):
                    if bit == 0:
                        symbol_literals.append(f'!{bdd_unique_vars[i]}')
                    elif bit == 1:
                        symbol_literals.append(f'{bdd_unique_vars[i]}')
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
                for v in bdd_unique_vars:
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


AST_TO_LATEX_TREE_TABLE = {
    'forall': '\\forall',
    'exists': '\\exists',
    'and': '\\land',
    'or': '\\lor',
    '->': '\\rightarrow',
    'not': '\\neg',
}


def _math_node(contents: str) -> str:
    return '\\node {$' + contents + '$}\n'

def _child_node(contents: str, tab_prefix: str) -> str:
    return tab_prefix + 'child{\n' + contents + tab_prefix + '}\n'

def _convert_ast_into_latex_tree(ast: AST_Node, depth: int = 0) -> str:
    """
    Convert given ast into a latex TikZ tree.
    
    Requires that the ast is FOL formula - it cannot contain let expressions.
    """
    tab_prefix = '\t' * depth

    if isinstance(ast, str):
        # The current node is a variable - construct a tree node
        return tab_prefix + _math_node(ast)
    elif isinstance(ast, Relation):
        # Handle atomic relations
        atom: Relation = ast
        return tab_prefix + _math_node(ast.into_string(use_latex_notation=True))
    node_type = ast[0]

    # Handle quantifiers / logical connectives
    latex_node_label = AST_TO_LATEX_TREE_TABLE.get(node_type)

    if not latex_node_label:
        raise ValueError(f'Cannot convert formula to latex tree - unknown node type: {node_type}')
    
    # Construct the part of the latex tree for this node
    if node_type in {'forall', 'exists'}:
        # Add variables being bound to quantifier tree nodes 
        bound_vars = (var for var, dummy_var_type in ast[1])
        latex_node_label = '{0}({1})'.format(latex_node_label, ', '.join(bound_vars))

        # Construct an unary tikz node
        current_node = tab_prefix + _math_node(latex_node_label)
        return current_node + _child_node(_convert_ast_into_latex_tree(ast[2], depth+1), tab_prefix)
    elif node_type in {'and', 'or'}:
        # Handle n-ary connectives - make n-ary node in the resulting tree
        latex_subtrees = (
            _child_node(_convert_ast_into_latex_tree(subtree, depth+1), tab_prefix) for subtree in ast[1:]
        )
        current_node = tab_prefix + _math_node(latex_node_label)
        return current_node + ''.join(latex_subtrees)
    elif node_type in {'not'}:
        # Construct an unary tikz node
        current_node = tab_prefix + _math_node(latex_node_label)
        return tab_prefix + current_node + _child_node(_convert_ast_into_latex_tree(ast[1], depth+1), tab_prefix)


def convert_ast_into_latex_tree(ast: AST_Node):
    return _convert_ast_into_latex_tree(ast, depth=0) + ';'
