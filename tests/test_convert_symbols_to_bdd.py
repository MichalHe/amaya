import pytest
from transitions import Symbol, constuct_bdd_from_transition_symbols, get_symbols_intersection
from typing import Tuple, List
from dd.autoref import BDD


@pytest.fixture()
def symbols() -> Tuple[Tuple[str, ...], List[Symbol]]:
    symbols = [
        ('*', 1, 0),
        (1, 1, 1),
        (0, 1, 0),
    ]

    var_names = ('a', 'b', 'c')

    return (var_names, symbols)


def test_conversion(symbols: Tuple[Tuple[str, ...], List[Symbol]]):
    var_names, syms = symbols
    bdd_manager = BDD()
    bdd_manager.declare(*var_names)
    e = constuct_bdd_from_transition_symbols(syms, var_names, bdd_manager)

    assert e
    models = list(bdd_manager.pick_iter(e))

    assert len(models) == 3

    expected_models = [
        (False, True, False),
        (True, True, True),
        (True, True, False),
    ]

    # reduce the mapping variable => bool, into evaluation tuple
    _models = list(map(lambda et: (et['a'], et['b'], et['c']), models))

    for em in expected_models:
        assert em in _models


def test_intersection():
    var_names = ('a', 'b', 'c', 'd')

    s0 = [
        ('*', 1, 0, 1),
        (1, 1, 1, 0),
        (1, 0, 1, 1),
    ]

    s1 = [
        (1, 0, 1, '*'),
    ]

    bdd_manager = BDD()
    bdd_manager.declare(*var_names)

    syms = get_symbols_intersection(s0, s1, var_names, bdd_manager)
    assert len(syms) == 1
    assert (1, 0, 1, 1) in syms