from collections import (
    deque,
    defaultdict,
)
from random import randint
from typing import (
    Any,
    Callable,
    Dict,
    Deque,
    Generator,
    Iterable,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    TypeVar,
    Union,
)

from amaya.stats import AutomatonInfo, StatPoint
from graphviz import Digraph


T = TypeVar('T')
S = TypeVar('S')

ColorPalette = List[Tuple[str, str]]

COLOR_PALETTE = [  # Node (bg, fg)
    ('#005e73', 'white'),
    ('#0B9396', 'black'),
    ('#94D2BC', 'black'),
    ('#E8D8A6', 'black'),
    ('#EE9B01', 'black'),
    ('#CA6701', 'white'),
    ('#BC3E03', 'black'),
    ('#AF2012', 'white'),
    ('#001219', 'white'),
    ('#9B2326', 'white'),
    ('#b5179e', 'black'),
    ('#606c38', 'white'),
    ('#560bad', 'white'),
    ('#4361ee', 'white'),
]


def vector_dot(vec1: Sequence[Union[int, str]], vec2: Sequence[Union[int, str]]) -> int:
    assert len(vec1) == len(vec2), 'Cannot take dot product of vectors with different length.'
    return sum(0 if '*' in c_pair else c_pair[0] * c_pair[1] for c_pair in zip(vec1, vec2))


def number_to_bit_tuple(number: int,
                        tuple_size: Optional[int] = None,
                        pad: int = 0) -> Tuple[int, ...]:
    bits: List[int] = []
    if number == 0:
        if tuple_size:
            return tuple([0] * tuple_size)
        return (0,)
    while number:
        bits.append(number % 2)
        number = int(number / 2)

    if tuple_size and len(bits) < tuple_size:
        missing_padding_c = tuple_size - len(bits)
        # Add missing padding
        bits += [0] * missing_padding_c
    return tuple(reversed(bits))


def carthesian_product(op0: Iterable[T], op1: Iterable[S]) -> List[Tuple[T, S]]:
    product: List[Tuple[T, S]] = list()

    for a in op0:
        for b in op1:
            product.append((a, b))

    return product


def reorder_variables_according_to_ids(variable_id_pairs: List[Tuple[str, int]],
                                       variables_with_coefficients: Tuple[List[str], List[int]]) -> Tuple[List[str], List[int]]:
    """
    Reorder the variables and their coefficients so that they match the order given by their IDs sorted.

    Example:
        variable_id_pairs = [('x', 2), ('y', 1)]
        variable_with_coefficients = (['x', 'y'], [10, 12])
        returns: (['y', 'x'], [12, 10])
    """

    variable_id_pairs_sorted = sorted(variable_id_pairs, key=lambda pair: pair[1])
    variable_to_coef_map: Dict[str, int] = dict(zip(*variables_with_coefficients))

    variables_ordered = []
    coefficients_ordered = []
    for var, dummy_id in variable_id_pairs_sorted:
        variables_ordered.append(var)
        coefficients_ordered.append(variable_to_coef_map.get(var))

    return (variables_ordered, coefficients_ordered)


def _dfs(graph: Dict[T, Iterable[T]],
         start_vertex: T,
         traversal_postorder: Deque[T],
         explored_vertices: Set[T]):
    """
    Recursive implementation of the depth first search made for the SCC searching kosaraju algorithm.

    :param graph: Graph to traverse (without labels).
    :param start_vertex: Vertex to start the DFS from.
    :param traversal_postorder: Will be populated with the order of the traversed vertices
                                (postorder) - topological sort.
    :param explored_vertices: Vertices already explored.
    :returns: Does not return anything - the search only populates the given traversal_postorder.
    """
    explored_vertices.add(start_vertex)
    for successor in graph.get(start_vertex, tuple()):
        if successor not in explored_vertices:
            _dfs(graph, successor, traversal_postorder, explored_vertices)
    traversal_postorder.append(start_vertex)


def find_sccs_kosaruju(graph: Dict[T, Iterable[T]]) -> Set[Tuple[T]]:
    """
    Finds and returns all SCCs in the given graph using the Kosaruju algorithm.

    Kosaraju algorithm is works by using a DFS and recording the traversed vertices upon
    exit (postorder) to calculate topological sort on the nodes.
    The graph is transposed (reversed), and the topological sort is used to give order of vertices from which DFS will
    be executed, identifying SCCs.

    :param graph: Graph given by a dictionary mapping vertices to their successors.
    :returns: Set of identified SCCs. The SCCs are stored in a sorted manner.
    """
    if not graph:
        return set()

    # Reverse the given graph
    rev_graph = defaultdict(list)
    for origin, destinations in graph.items():
        for dest in destinations:
            rev_graph[dest].append(origin)

    vertices = set(graph.keys()).union(rev_graph.keys())
    explored_vertices = set()

    topological_sort: Deque[T] = deque()
    while vertices:
        current_vertex = next(iter(vertices))
        _dfs(graph, current_vertex, topological_sort, explored_vertices)
        vertices = vertices.difference(explored_vertices)

    # Use the computed topological sort on DFS throught the reversed graph to find SCCs
    explored_vertices = set()
    sccs = set()
    current_scc = []
    while topological_sort:
        current_vertex = topological_sort.pop()
        if current_vertex in explored_vertices:
            continue

        current_scc = deque()
        _dfs(rev_graph, current_vertex, current_scc, explored_vertices)
        sccs.add(tuple(sorted(current_scc)))

    return sccs


def get_color_palette_with_min_size(min_palette_size: int) -> ColorPalette:
    """
    Constructs a color palette with size at least as big as the requirested size.

    The color palette has the first 14 colors defined by hand. If the requested palette is is greater than 14,
    the missing colors are generated randomly.

    :param min_palette_size: The minimal number of colors to present in the palette.
    :return: The requested color palette at least as big as the requested size.
    """
    if min_palette_size <= len(COLOR_PALETTE):
        return COLOR_PALETTE
    else:
        missing_color_cnt = min_palette_size - len(COLOR_PALETTE)
        random_colors = ['{r:02x}{g:02x}{b:02x}' for r, g, b in (
                            (randint(0, 255), randint(0, 255), randint(0, 255)) for i in range(missing_color_cnt)
                        )]
        return list(COLOR_PALETTE) + random_colors


def _construct_newick_tree_from_trace(root: StatPoint, output_id_to_op_table: Dict[int, StatPoint]) -> str:
    # print(root.output.automaton_id)
    if not root.operand1 and not root.operand2:
        return f'{root.operation.value}:{root.output.size}'

    if root.operand1 and not root.operand2:
        op = output_id_to_op_table[root.operand1.automaton_id]
        operand1_str = _construct_newick_tree_from_trace(op, output_id_to_op_table)
        return f'({operand1_str},{root.operation.value}:{root.output.size})'
    if root.operand2 and not root.operand1:
        op = output_id_to_op_table[root.operand2.automaton_id]
        operand2_str = _construct_newick_tree_from_trace(op, output_id_to_op_table)
        return f'({operand2_str},{root.operation.value}:{root.output.size})'

    assert root.operand1 and root.operand2

    op1 = output_id_to_op_table[root.operand1.automaton_id]
    operand1_str = _construct_newick_tree_from_trace(op1, output_id_to_op_table)

    op2 = output_id_to_op_table[root.operand2.automaton_id]
    operand2_str = _construct_newick_tree_from_trace(op2, output_id_to_op_table)
    return f'({operand1_str},{root.operation.value}:{root.output.size},{operand2_str})'


def construct_newick_tree_from_trace(trace: List[StatPoint]) -> str:
    operands = set()
    for op in trace:
        if op.operand1:
            operands.add(op.operand1.automaton_id)
        if op.operand2:
            operands.add(op.operand2.automaton_id)

    roots = [op for op in trace if op.output.automaton_id not in operands]
    if len(roots) > 1:
        raise ValueError(f'Cannot construct newick tree from given trace - there are multiple root nodes in the tree.')
    root = roots[0]

    output_id_to_op_table = {op.output.automaton_id: op for op in trace}

    return _construct_newick_tree_from_trace(root, output_id_to_op_table)


def construct_dot_tree_from_trace(trace: List[StatPoint]) -> str:
    graph = Digraph('traceviz', strict=True, graph_attr={'rankdir': 'LR', 'ranksep': '1'})
    for op in trace:
        graph.node(str(op.output.automaton_id), f'{op.operation.value}, size={op.output.size}, ID={op.operation_id}')
    for op in trace:
        if op.operand1:
            graph.edge(str(op.output.automaton_id), str(op.operand1.automaton_id))
        if op.operand2:
            graph.edge(str(op.output.automaton_id), str(op.operand2.automaton_id))

    return str(graph)
