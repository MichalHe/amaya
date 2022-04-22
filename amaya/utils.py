from collections import (
    deque,
    defaultdict,
)
from typing import (
    Any,
    Callable,
    Dict,
    Deque,
    Generator,
    Iterable,
    List,
    Optional,
    Set,
    Tuple,
    TypeVar,
)

T = TypeVar('T')
S = TypeVar('S')
DebugStateTranslationFn = Callable[[S, int], None]


def vector_dot(vec1, vec2) -> int:
    assert(len(vec1) == len(vec2))
    sum_ = 0
    for a, b in zip(vec1, vec2):
        sum_ += 0 if a == '*' or b == '*' else a*b
    return sum_


def search_tree(tree, searched_token):
    if not type(tree) == list:
        return None
    current_node_token = tree[0]
    if current_node_token == searched_token:
        return tree  # Return whole subtree
    else:
        for subtree in tree[1:]:
            match = search_tree(subtree, searched_token)
            if match:
                return match
        return None


def tree_depth(tree) -> int:
    if type(tree) != list or len(tree) == 0:
        return 0

    max_depth = 0
    for leaf in tree:  # first leaf is the node name
        max_depth = max((tree_depth(leaf), max_depth))
    return max_depth + 1


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


def transition_fn_size(fn: Dict[Any, Dict[Any, Iterable[Any]]]) -> int:
    size = 0
    for origin in fn:
        for symbol in fn[origin]:
            for dest in fn[origin][symbol]:
                size += 1
    return size


def iter_transition_fn(fn: Dict[S, Dict[Tuple[int, ...], Iterable[S]]]) -> Generator[Tuple[S, Tuple[int, ...], S], None, None]:
    for o in fn:
        for s in fn[o]:
            for d in fn[o][s]:
                yield (o, s, d)


def copy_transition_fn(fn: Dict[S, Dict[Tuple[int, ...], Set[S]]]) -> Dict[S, Dict[Tuple[int, ...], Set[S]]]:
    new_fn: Dict[S, Dict[Tuple[int, ...], Set[S]]] = {}
    for src in fn:
        new_fn[src] = {}
        for sym in fn[src]:
            new_fn[src][sym] = set(fn[src][sym])
    return new_fn


def create_enumeration_state_translation_map(states: Iterable[S],
                                             debug_rename_function: Optional[DebugStateTranslationFn] = None,
                                             start_from=0
                                             ) -> Tuple[int, Dict[S, int]]:
    state_cnt = start_from
    translation: Dict[S, int] = {}
    for state in states:
        new_state_name = state_cnt
        if (debug_rename_function is not None):
            debug_rename_function(state, new_state_name)

        translation[state] = new_state_name
        state_cnt += 1
    return (state_cnt, translation)


def reorder_variables_according_to_ids(variable_id_pairs: List[Tuple[str, int]],
                                       variables_with_coeficients: Tuple[List[str], List[int]]) -> Tuple[List[str], List[int]]:
    '''
    Reorder the variables and their coeficients so that they match the order given by their IDs sorted.

    Example:
        variable_id_pairs = [('x', 2), ('y', 1)]
        variable_with_coeficients = (['x', 'y'], [10, 12])
        returns: (['y', 'x'], [12, 10])
    '''

    variable_id_pairs_sorted = sorted(variable_id_pairs, key=lambda pair: pair[1])
    variable_to_coef_map: Dict[str, int] = dict(zip(*variables_with_coeficients))

    variables_ordered = []
    coeficients_ordered = []
    for var, dummy_id in variable_id_pairs_sorted:
        variables_ordered.append(var)
        coeficients_ordered.append(variable_to_coef_map.get(var))

    return (variables_ordered, coeficients_ordered)


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
