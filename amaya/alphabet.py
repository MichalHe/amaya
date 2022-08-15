from __future__ import annotations
from dataclasses import dataclass
from typing import (
    Dict,
    List,
    Set,
    Any,
    Tuple,
    Generator,
    Iterable,
    Union,
    Optional
)
from amaya.utils import number_to_bit_tuple
from amaya.relations_structures import Relation


LSBF_AlphabetSymbol = Tuple[Union[int, str], ...]


@dataclass
class LSBF_Alphabet():
    variable_names: Dict[int, str]
    variable_numbers: List[int]
    active_variables: Set[str]
    active_symbols: Optional[Tuple[LSBF_AlphabetSymbol, ...]] = None

    def gen_projection_symbols_onto_variables(self, variables_subset: List[int]) -> Generator[Tuple[int, ...], Any, Any]:
        """
        Generate alphabet symbols of an alphabet for the variables_subset.
        """
        # We actually do not care about the subset passed in, we just generate
        # bit vectors of given length
        symbol_size = len(variables_subset)
        for i in range(2**len(variables_subset)):
            bit_vector = number_to_bit_tuple(i, tuple_size=symbol_size)
            yield bit_vector

    def cylindrify_symbol_of_projected_alphabet(self,
                                                variables: List[int],
                                                symbol: Tuple[int, ...]) -> Tuple[Union[str, int], ...]:
        """
        Cylindrify the given symbol of an alphabet with given variables.

        Performs cylindrification on the given symbol that belongs to a smaller alphabet for a subset of variables
        of this alphabet.
        :param variables: A list of variables (ids) identifying the tracks of the symbol.
                          The ids needs to be sorted.
        :param symbol: Symbol with bits containing the values of `variables` tracks.
                       The symbol should contain 0/1/* for bit values, but this is not checked.
        :returns: The cylindrified symbol that belongs to this alphabet with don't care bits on tracks whose
                  variables are not in `variables`.
        """
        alphabet_size = len(self.variable_numbers)

        # Create a list of indices where we should put the values from the
        # provided symbol (rest will be '*')
        vi = 0  # Index of the next variable name in provided variables to be checked
        used_variables_cooficients = []
        for i, var_id in enumerate(self.variable_numbers):
            if var_id == variables[vi]:
                used_variables_cooficients.append(i)
                vi += 1

            if vi == len(variables):
                break

        ni = 0  # Index to the next bit in the given symbol that should be used.
        cylindrified_symbol: List = [None] * alphabet_size
        for i in range(alphabet_size):
            if i == used_variables_cooficients[ni]:
                cylindrified_symbol[i] = symbol[ni]
                ni += 1
                # All bits from the given symbol have been used, fill the rest
                # with *.
                if ni == len(symbol):
                    for j in range(i+1, alphabet_size):
                        cylindrified_symbol[j] = '*'
                    break
            else:
                cylindrified_symbol[i] = '*'
        return tuple(cylindrified_symbol)

    def cylindrify_projected_symbol_iter_all(self, symbol: LSBF_AlphabetSymbol, variables: List[int]):
        """
        Cylindrify the given projected symbol onto this alphabet and yield all symbols.

        Take the symbol that comes from an alphabet with a subset of variables
        and cylindrify it onto this alphabet. In order to know for to variables
        does the symbol bits belong, a list of the variables of the smaller
        alphabet is passed.

        :param symbol: Symbol of the alphabet for a subset of variables of this alphabet.
        :param variables: A sorted list of variables of the smaller alphabet.
        :returns: Generates all symbols that result from the cylindrification.
        """
        alphabet_size = len(self.variable_numbers)

        for rest_bits in range(2**(alphabet_size - len(variables))):
            variable_index = 0
            rest_bits_index = alphabet_size - len(variables) - 1
            cylindrified_symbol = [None] * alphabet_size
            for i, cylindrified_variable in enumerate(self.variable_numbers):
                if variable_index == len(variables):
                    # No more variables in the smaller alphabet, fill the rest with the bits from rest_bits
                    while rest_bits_index >= 0:
                        cylindrified_symbol[i] = ((rest_bits & (0x1 << rest_bits_index)) >> rest_bits_index)
                        i += 1
                        rest_bits_index -= 1
                    break
                if cylindrified_variable == variables[variable_index]:
                    cylindrified_symbol[i] = symbol[variable_index]
                    variable_index += 1
                else:
                    cylindrified_symbol[i] = ((rest_bits & (0x1 << rest_bits_index)) >> rest_bits_index)
                    rest_bits_index -= 1
            yield cylindrified_symbol

    def project_symbol_onto_variables(self, symbol: LSBF_AlphabetSymbol, variables: List[int]) -> LSBF_AlphabetSymbol:
        """
        Projects given symbol onto the variables.
        :param symbol: Symbol of this alphabet that should be projected onto given variables.
        :param variables: The sorted list containing a subset of variables of this alphabet to project the symbol on.
        :returns: The projected symbol.
        """
        projected_symbol = [None] * len(variables)
        variable_subset_index = 0

        for i, variable in enumerate(self.variable_numbers):
            if variable_subset_index == len(variables):
                break  # We've exhausted all variables, don't have to iterate any further.
            if variable == variables[variable_subset_index]:
                projected_symbol[variable_subset_index] = symbol[i]
                variable_subset_index += 1
        return projected_symbol

    def gen_symbols_for_relevant_variables(self,
                                           relevant_var_ids: List[int]) -> Generator[LSBF_AlphabetSymbol, None, None]:
        """
        Generate alphabet symbols to with bits only on tracks for variables with given IDs.

        Generate symbols for variable IDs with don't care bit '*' in place of other (non-relevant) variables.

        Assumes that the variable IDs used in this alphabet are sequentially assigned.
        """
        if not relevant_var_ids:
            yield tuple('*' for var_id in self.variable_numbers)
            return

        # Tracks/variable IDs are numbered from 1 due to MTBDD requirements
        for i in range(2**len(relevant_var_ids)):
            bits = number_to_bit_tuple(i, tuple_size=len(relevant_var_ids))

            # Use index to access var ids as it will be also used to grab the valid bit from bits for var track
            next_rel_var_id_i = 0

            symbol: List = [None] * len(self.variable_numbers)
            for i in range(len(self.variable_numbers)):
                if i == relevant_var_ids[next_rel_var_id_i] - 1:  # Tracks are ID'd from 1, subtract it
                    symbol[i] = bits[next_rel_var_id_i]
                    next_rel_var_id_i += 1

                    # Check if all nonzero track indices have been populated with bits, if yes pad rest with *
                    if next_rel_var_id_i == len(relevant_var_ids):
                        for j in range(i+1, len(self.variable_numbers)):
                            symbol[j] = '*'
                        break
                else:
                    symbol[i] = '*'
            
            yield tuple(symbol)

    @staticmethod
    def from_variable_ids(variable_ids: List[int]) -> LSBF_Alphabet:
        """
        Creates a new alphabet from the given variable_name, id pairs.

        The variables list should be sorted by the ID.
        """

        assert False, "This factory method should not be used anymore."
        variable_names: Dict[int, str] = dict()
        variable_ids = sorted(variable_ids)

        return LSBF_Alphabet(
            active_variables=set(),
            variable_names=variable_names,
            variable_numbers=variable_ids
        )

    @staticmethod
    def from_variable_id_pairs(var_id_pairs: Iterable[Tuple[str, int]]) -> LSBF_Alphabet:
        """
        Creates a new alphabet from the given variables with their identifiers.
        """
        var_ids: List[int] = []
        var_id_to_names: Dict[int, str] = {}
        for var_name, var_id in var_id_pairs:
            var_ids.append(var_id)
            var_id_to_names[var_id] = var_name

        var_ids = sorted(var_ids)

        return LSBF_Alphabet(
            active_variables=set(),
            variable_names=var_id_to_names,
            variable_numbers=var_ids,
        )

    @property
    def symbols(self):
        """
        Symbols of this alphabet.

        Iterator allowing to lazily iterate over the symbols of this alphabet.
        """
        letter_size = len(self.variable_numbers)
        for i in range(2**letter_size):
            yield number_to_bit_tuple(i, tuple_size=letter_size, pad=0)

    def assert_variable_names_to_ids_match(self,
                                           variable_id_pairs: Iterable[Tuple[str, int]]):
        """
        Checks that the given variables with their given IDs binding is present
        in the alphabet and is correct.

        The checks are performed via assertions, therefore, does not returns
        anything.
        """
        for var_name, var_id in variable_id_pairs:
            msg = (f'Given variable id: "{var_id}" is not known to the alphabet'
                   f'. Known ids: {self.variable_numbers}')
            assert var_id in self.variable_names, msg
            msg = ('Given variable name is bound to a different variable.'
                   f'Binding present {var_id}->"{self.variable_names[var_id]}",'
                   f' tried binding: {var_id}->"{var_name}.')
            assert self.variable_names[var_id] == var_name, msg


def uncompress_transition_symbol(symbol: LSBF_AlphabetSymbol) -> Generator[Tuple[int, ...], None, None]:
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
