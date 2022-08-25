from typing import Generator


def tokenize(smt2_text: str) -> Generator[str, None, None]:
    lexical_entity_start = 0

    is_inside_string = False
    is_inside_symbol = False
    is_inside_quoted_symbol = False

    for current_pos, char in enumerate(smt2_text):
        if is_inside_string:
            if char == '"':
                # Perform lookahead to check whether the current character is a escape char for other quote
                if not (len(smt2_text) > current_pos + 2 and smt2_text[current_pos+1] == '"'):
                    is_inside_string = False
                    yield smt2_text[lexical_entity_start:current_pos].replace('""', '"')
        elif is_inside_quoted_symbol:
            if char == '|':
                is_inside_quoted_symbol = False
                yield smt2_text[lexical_entity_start:current_pos]
        elif char == '"':
            is_inside_string = True
            lexical_entity_start = current_pos + 1
        elif char == '|':
            lexical_entity_start = current_pos + 1
            is_inside_quoted_symbol = True
        elif char in ('(', ')'):
            if is_inside_symbol:
                yield smt2_text[lexical_entity_start:current_pos]
                is_inside_symbol = False
            yield char
        else:
            if is_inside_symbol:
                if char.isspace():
                    yield smt2_text[lexical_entity_start:current_pos]
                    is_inside_symbol = False
            else:
                if not char.isspace():
                    is_inside_symbol = True
                    lexical_entity_start = current_pos
