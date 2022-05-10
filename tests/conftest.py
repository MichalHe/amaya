class ResolutionState:
    """
    Class enabling description of the structure of automata with low level 
    of nondeterminism from initial state deeper into the structure and validating
    that an automaton matches the description.
    """
    def __init__(self, _id: str = ''):
        self.automaton_state = None
        self._id = _id

    def bind(self, real_automaton_state):
        if self.automaton_state is not None:
            if self.automaton_state != real_automaton_state:
                raise ValueError('Attempting to rebind automaton state value! Current: {0} New {1}'.format(
                    self.automaton_state, real_automaton_state
                ))
        else:
            self.automaton_state = real_automaton_state

    def is_bound(self):
        return self.automaton_state is not None

    def get(self):
        if self.automaton_state is None:
            raise ValueError(f'{self._id} Attempting to read from resolvent state without assigning the value first.')
        return self.automaton_state

    def __repr__(self) -> str:
        return f'State(value={self.automaton_state}, id={self._id})'

    def __eq__(self, other) -> bool:
        if isinstance(other, ResolutionState):
            return self.automaton_state == other.automaton_state and self._id == other._id
        else:
            return False

    def __hash__(self):
        return hash((self.automaton_state, self._id))
