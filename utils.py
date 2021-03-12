from typing import Tuple, List, Optional, Iterable, TypeVar, Any, Dict, Generator, Callable, Set

T = TypeVar('T')
S = TypeVar('S')
DebugStateTranslationFn = Callable[[S, int], None]


def vector_dot(vec1, vec2) -> int:
    assert(len(vec1) == len(vec2))
    sum_ = 0
    for a, b in zip(vec1, vec2):
        sum_ += a*b
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


K = TypeVar('K')
def get_default_if_none(maybe_none: Optional[K], default: Callable[[], K]) -> K:
    if maybe_none is None:
        return default()
    else:
        return maybe_none