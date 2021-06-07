from typing import Dict, List

UNICODE_SYMBOLS = {
    'and': '∧',
    'or': '∨',
    'exists': '∃',
    'forall': '∀',
}


def variable_needs_translation(variable_name: str) -> bool:
    '''This should be extended some day to contain regex'''
    if variable_name[0] == '?':
        return True
    return False


def get_translation(variable_name: str) -> str:
    return variable_name.replace('?', '')


def get_binding_variables(binding) -> List[str]:
    variables = []
    for bind in binding:
        variables.append(bind[0])
    return variables


def translate_variables_if_needed(variables, translations: Dict[str, str]):
    for i, variable in enumerate(variables):
        if variable_needs_translation(variable):
            translated_var = get_translation(variable)
            translations[variable] = translated_var
            variables[i] = translated_var
    return variables


def get_presburger_human_readable(smt_presburger, translations: Dict[str, str] = {}) -> str:
    '''We need to reshuffle the AST to get something human can read'''

    if type(smt_presburger) == list:
        node_name = smt_presburger[0]
        if node_name in ['<', '>', '<=', '>=', '=', '+', '*']:
            lhs = get_presburger_human_readable(smt_presburger[1], translations)
            rhs = get_presburger_human_readable(smt_presburger[2], translations)
            if node_name in ['+', '*']:
                return f'{lhs}{node_name}{rhs}'
            return f'{lhs} {node_name} {rhs}'
        elif node_name == '-':
            if len(smt_presburger) == 2:
                neg_expr = get_presburger_human_readable(smt_presburger[1], translations)
                return f'-{neg_expr}'
            else:
                lhs = get_presburger_human_readable(smt_presburger[1], translations)
                rhs = get_presburger_human_readable(smt_presburger[2], translations)
                return f'{lhs}{node_name}{rhs}'
        else:
            print(smt_presburger)
            return "Err"
    else:
        atom = smt_presburger
        if atom in translations:
            return translations[atom]
        else:
            if type(atom) == str:
                if variable_needs_translation(atom):
                    translations[atom] = get_translation(atom)
                    return translations[atom]
                else:
                    return atom
            return str(atom)


def translate_smtformula_to_human_readable(smt_formula,
                                           translated_variables: Dict[str, str] = {}) -> str:
    # ['not',
    #  ['and',
    #   ['<=', '?X', 0],
    #   ['<=', '?Y', 0]
    #   ]
    #  ]

    node_name: str = smt_formula[0]
    if node_name == 'not':
        subterm = translate_smtformula_to_human_readable(smt_formula[1], translated_variables)
        return f'¬({subterm})'
    elif node_name in ['and', 'or']:
        subterm1 = translate_smtformula_to_human_readable(smt_formula[1], translated_variables)
        subterm2 = translate_smtformula_to_human_readable(smt_formula[2], translated_variables)
        return f'( ({subterm1}) {UNICODE_SYMBOLS[node_name]} ({subterm2}) )'
    elif node_name in ['exists', 'forall']:
        symbol = UNICODE_SYMBOLS[node_name]
        binding_variables = get_binding_variables(smt_formula[1])
        translate_variables_if_needed(binding_variables, translated_variables)
        binding = ','.join(binding_variables)
        subterm = translate_smtformula_to_human_readable(smt_formula[2], translated_variables)
        return f' {symbol}{binding}({subterm})'
    else:
        return get_presburger_human_readable(smt_formula, translated_variables)
