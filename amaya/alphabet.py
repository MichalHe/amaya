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
from amaya.relations_structures import Relation, Var


LSBF_AlphabetSymbol = Tuple[Union[int, str], ...]


@dataclass
class LSBF_Alphabet():
    all_vars: List[Var]

    def gen_projection_symbols_onto_variables(self, variables_subset: List[Var]) -> Generator[Tuple[int, ...], Any, Any]:
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
                                                variables: List[Var],
                                                symbol: Tuple[int, ...]) -> Tuple[Union[str, int], ...]:
        """
        Cylindrify the given symbol of an alphabet with given variables.

        Performs cylindrification on the given symbol that belongs to a smaller alphabet for a subset of variables
        of this alphabet.
        :param variables: A sorted list of variables (IDs) identifying the tracks of the symbol.
        :param symbol: Symbol with bits containing the values of `variables` tracks.
                       The symbol should contain 0/1/* for bit values, but this is not checked.
        :returns: The cylindrified symbol that belongs to this alphabet with don't care bits on tracks whose
                  variables are not in `variables`.
        """
        if not variables:
            return tuple('*' for num in self.all_vars)

        alphabet_size = len(self.all_vars)

        # Create a list of indices where we should put the values from the
        # provided symbol (rest will be '*')
        vi = 0  # Index of the next variable name in provided variables to be checked
        used_variables_cooficients = []
        for i, var in enumerate(self.all_vars):
            if var == variables[vi]:
                used_variables_cooficients.append(i)
                vi += 1

            if vi == len(variables):
                break

        ni = 0  # Index to the next bit in the given symbol that should be used.
        cylindrified_symbol: List[Union[str, int]] = [0] * alphabet_size
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

    def gen_symbols_for_relevant_variables(self, relevant_vars: List[Var]) -> Generator[LSBF_AlphabetSymbol, None, None]:
        """
        Generate alphabet symbols to with bits only on tracks for variables with given IDs.

        Generate symbols for variable IDs with don't care bit '*' in place of other (non-relevant) variables.

        Assumes that the variable IDs used in this alphabet are sequentially assigned.
        """
        if not relevant_vars:
            yield tuple('*' for var_id in self.all_vars)
            return

        # Tracks/variable IDs are numbered from 1 due to MTBDD requirements
        for i in range(2**len(relevant_vars)):
            bits = number_to_bit_tuple(i, tuple_size=len(relevant_vars))

            # Use index to access var ids as it will be also used to grab the valid bit from bits for var track
            next_rel_var_id_i = 0

            symbol: List[Union[str, int]] = [0] * len(self.all_vars)
            for i in range(len(self.all_vars)):
                if i == relevant_vars[next_rel_var_id_i].id - 1:  # Tracks are ID'd from 1, subtract it
                    symbol[i] = bits[next_rel_var_id_i]
                    next_rel_var_id_i += 1

                    # Check if all nonzero track indices have been populated with bits, if yes pad rest with *
                    if next_rel_var_id_i == len(relevant_vars):
                        for j in range(i+1, len(self.all_vars)):
                            symbol[j] = '*'
                        break
                else:
                    symbol[i] = '*'

            yield tuple(symbol)


    @staticmethod
    def from_vars(vars: Iterable[Var]) -> LSBF_Alphabet:
        """
        Creates a new alphabet from the given variables with their identifiers.
        """
        all_vars = sorted(vars)
        return LSBF_Alphabet(all_vars=all_vars)

    @property
    def symbols(self):
        """
        Symbols of this alphabet.

        Iterator allowing to lazily iterate over the symbols of this alphabet.
        """
        letter_size = len(self.all_vars)
        for i in range(2**letter_size):
            yield number_to_bit_tuple(i, tuple_size=letter_size, pad=0)


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
