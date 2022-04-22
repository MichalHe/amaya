from typing import (
    Dict,
    Tuple,
    Set,
)

from amaya.utils import find_sccs_kosaruju

import pytest


@pytest.mark.parametrize(
    ('graph', 'expected_scss'),
    (
        ({0: (1, 2)}, {(0,), (1,), (2,)}),
        ({0: (1, 2), 1: (1,)}, {(0,), (1,), (2,)}),
        ({0: (1,), 1: (2,), 2: (0,)}, {(0, 1, 2)}),
        ({0: (1,), 1: (2,), 2: (0,), 3: (4, )}, {(0, 1, 2), (3,), (4,)}),
        ({0: (1,), 1: (2,), 2: (0,), 3: (4, 5), 5: (3,)}, {(0, 1, 2), (3, 5), (4,)}),
    )
)
def test_find_sccs_simple(graph: Dict[int, Tuple[int]], expected_scss: Set[Tuple[int]]):
    actual = find_sccs_kosaruju(graph)
    assert actual == expected_scss
