from enum import IntEnum
from typing import List, Any

_AstNodeTypes = [
    'SetInfo',
    'SetLogic',
    'Asset',
    'CheckSat',
    'Exit'
]

_TokenTypes = [
    'L_PAREN',
    'R_PAREN',
    'STR',
    'QUOTED_SYMBOL',
    'ID',
    'NUMBER'
]

ASTNodeType = IntEnum('ASTNodeType', _AstNodeTypes)
TokenType = IntEnum('TokenType', _TokenTypes)


class Token():
    def __init__(self, type: TokenType, contents: Any = None):
        self.type = type
        self.contents = contents

    def __repr__(self) -> str:
        tk_types_with_no_contents = [
            TokenType.L_PAREN,
            TokenType.R_PAREN
        ]

        if self.type in tk_types_with_no_contents:
            return f'Token(type={self.type.name})'
        else:
            return f'Token(type={self.type.name}, {self.contents})'


class ASTNode():
    def __init__(self, node_type: ASTNodeType):
        self.type = node_type


class ASTBinaryNode(ASTNode):
    def __init__(self, node_type: ASTNodeType, left: ASTNode, right: ASTNode):
        self.left = left
        self.right = right
        super().__init__(node_type)


class ASTUnaryNode(ASTNode):
    def __init__(self, node_type: ASTNodeType, child: ASTNode):
        self.child = child
        super().__init__(node_type)


class ASTNaryNode(ASTNode):
    def __init__(self, node_type: ASTNodeType, children: List[ASTNode]):
        self.children = children
        super().__init__(node_type)


def lex_identifier(src_text: str, pos: int):
    start = pos

    while src_text[pos] != ' ':
        pos += 1
    end = pos

    return src_text[start:end]


def lex_string(src_text: str, start: int):
    start += 1  # Skip the " at the beginning
    is_quoted = False

    pos = start
    found_str_end = False
    while (not found_str_end) and pos < len(src_text):
        current_char = src_text[pos]
        if current_char == '"':
            if is_quoted:
                is_quoted = False  # clear out the quote (was used)
            else:
                if pos + 1 < len(src_text):
                    next_char = src_text[pos+1]
                    if next_char == '"':
                        is_quoted = True
                    else:
                        found_str_end = True
                else:
                    found_str_end = True

        pos += 1

    if not found_str_end:
        raise ValueError('Could not locate string end')
    else:
        return src_text[start:pos-1], pos


def lex_quoted_symbol(src_text: str, start: int):
    start += 1  # Skip the " at the beginning

    pos = start
    found_symbol_end = False
    while (not found_symbol_end) and pos < len(src_text):
        current_char = src_text[pos]
        if current_char == '|':
            found_symbol_end = True
        elif current_char == '\\':
            # \ cannot be contained inside quoted symbol
            raise ValueError('Error while parsing quoted symbol - cannot contain \'\\\'')
        pos += 1

    if not found_symbol_end:
        raise ValueError('Could not locate quoted symbol end (reached EOF)')
    else:
        return src_text[start:pos-1], pos


def lex(src_text):
    pos = 0
    tokens = []
    while pos < len(src_text):
        current_char = src_text[pos]
        if current_char == '(':
            tk = Token(TokenType.L_PAREN)
            tokens.append(tk)
            pos += 1
        elif current_char == ')':
            tk = Token(TokenType.R_PAREN)
            tokens.append(tk)
            pos += 1
        elif current_char == '"':
            s, end = lex_string(src_text, pos)
            tokens.append(Token(TokenType.STR, contents=s))
            pos = end
        elif current_char == '|':
            qs, end = lex_quoted_symbol(src_text, pos)
            tokens.append(Token(TokenType.QUOTED_SYMBOL, contents=qs))
            pos = end
        elif current_char.isspace():
            pos += 1
        else:
            # Might be number, or
    return tokens
