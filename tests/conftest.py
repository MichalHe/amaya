class ResolutionState:
    def __init__(self):
        self.automaton_state = None

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
            raise ValueError('Attempting to read from resolvent state without assigning the value first.')
        return self.automaton_state
