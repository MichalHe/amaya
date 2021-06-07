from enum import IntEnum
from typing import List, Any, Tuple

_AstNodeTypes = [
    'set-info',
    'set-logic',
    'assert',
    'check-sat',
    'exit',
    'exists',
    'not',

    # Binary relational operators
    'LESS',
    'LESS_EQ',
    'GREATER',
    'GREATER_EQ',


    'IDENTIF',
    'NUMBER',
    'TYPE_BINDING',
    'LIST'
]

_TokenTypes = [
    'L_PAREN',
    'R_PAREN',
    'COLON',
    'STR',
    'QUOTED_SYMBOL',
    'IDENTIF',
    'NUMBER',
    'LESS_EQ',
    'LESS',
    'GREATER_EQ',
    'GREATER',
    'EQ',
    'NEQ',
    'PLUS',
    'SUB',
    'MUL',
]

ASTNodeType = IntEnum('ASTNodeType', _AstNodeTypes)
TokenType = IntEnum('TokenType', _TokenTypes)


class ASTBuildingException(Exception):
    pass


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

    def __repr__(self):
        return f'BinaryNode({self.type.name}, left: {self.left}, right: {self.right})'


class ASTUnaryNode(ASTNode):
    def __init__(self, node_type: ASTNodeType, child: ASTNode):
        self.child = child
        super().__init__(node_type)

    def __repr__(self):
        return f'ASTUnaryNode({self.type.name}, {self.child})'


class ASTNaryNode(ASTNode):
    def __init__(self, node_type: ASTNodeType, children: List[ASTNode]):
        self.children = children
        super().__init__(node_type)

    def __repr__(self):
        return f'ASTUnaryNode({self.type.name}, {self.children})'


class ASTAtomNode(ASTNode):
    def __init__(self, node_type: ASTNodeType, contents: Any = None):
        super().__init__(node_type)
        self.contents = contents

    def __repr__(self):
        if self.contents is not None:
            return f'Atom({self.type.name}, {self.contents})'
        else:
            return f'Atom({self.type.name})'


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


def lex_identifier(src_text: str, start: int) -> Tuple[str, int]:
    '''Lexes identifier from start, until whitespace is found

    returns:
        Tuple, where the first item is the parsed identifier, the other one
        is the end, where the lexing stopped.
    '''
    # import pdb
    # pdb.set_trace()

    # TODO: Write regex for this :(
    pos = start
    current_char = src_text[pos]
    is_valid = current_char.isalnum() or current_char in ['?']
    while pos < len(src_text) and is_valid:
        pos += 1
        current_char = src_text[pos]
        is_valid = current_char.isalnum() or current_char in ['-', '.', '?']
    return src_text[start:pos], pos


def lex_operator(src_text: str, pos: int) -> Token:
    current_char = src_text[pos]
    has_next_char = pos < len(src_text)

    operator_2_tk_type = {
        '<': TokenType.LESS_EQ,
        '<=': TokenType.LESS,
        '>': TokenType.GREATER_EQ,
        '>=': TokenType.GREATER,
        '=': TokenType.EQ,
        '!=': TokenType.NEQ,

        '+': TokenType.PLUS,
        '-': TokenType.SUB,
        '*': TokenType.MUL,
    }

    if current_char in ['<', '>']:
        if has_next_char:
            if src_text[pos+1] == '=':
                return operator_2_tk_type[current_char + '='], 2
        return operator_2_tk_type[current_char], 1

    if current_char in ['+', '-', '*']:
        return operator_2_tk_type[current_char], 1

    if current_char == '=':
        return TokenType.EQ, 1
    elif current_char == '!':
        if has_next_char:
            if src_text[pos+1] == '=':
                return TokenType.NEQ, 2
            else:
                raise ValueError('Unknown operator: !')
        else:
            raise ValueError('Unknown operator: !')


def lex(src_text) -> List[Token]:
    '''Breaks up the source text into lexems

    returns:
        List of found tokens
    '''
    pos = 0
    tokens = []
    operators_first_char = ['<', '>', '=', '!', '-', '+', '*']
    while pos < len(src_text):
        current_char = src_text[pos]
        if current_char.isspace():
            pos += 1
            continue

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
        elif current_char == ':':
            tokens.append(Token(TokenType.COLON))
            pos += 1
        elif current_char in operators_first_char:
            operator_type, width = lex_operator(src_text, pos)
            tokens.append(Token(operator_type))
            pos += width
        else:
            identifier, end = lex_identifier(src_text, pos)
            # Identifier might be in fact number
            try:
                num = int(identifier)
                tokens.append(Token(TokenType.NUMBER, num))
            except ValueError:
                tokens.append(Token(TokenType.IDENTIF, identifier))
            pos = end
    return tokens


def mk_atomic_node_if_needed(maybe_token) -> ASTNode:
    if type(maybe_token) == Token:
        atom_type = ASTNodeType[maybe_token.type.name]
        return ASTAtomNode(atom_type, contents=maybe_token.contents)
    else:
        # It is actually an AST Node processed before
        return maybe_token


def make_ast_for_type_binding(node_list: List[Any]) -> ASTNode:
    var_name, var_type = node_list
    return ASTBinaryNode(ASTNodeType.TYPE_BINDING, var_name, var_type)


def make_ast_for_list(node_list: List[Any]) -> ASTNode:
    return ASTNaryNode(ASTNodeType.LIST, node_list)

def make_ast_node_from_list(node_list: List[Any]) -> ASTNode:
    node_name_tk = node_list[0]

    binary_rel_ops = [
        TokenType.LESS,
        TokenType.GREATER,
        TokenType.LESS_EQ,
        TokenType.GREATER_EQ,
    ]

    # KW : Children count
    keywords = {
        'set-info'  : 3,
        'set-logic' : 2,
        'assert'     : 2,
        'check-sat' : 1,
        'exit'      : 1,
        'exists'    : 3,
        'not'       : 2,
    }

    if node_name_tk.type in binary_rel_ops:
        # Check the node is valid
        if not len(node_list) == 3:
            raise ASTBuildingException(f'Binary node has not valid number of children: {len(node_list) - 1}/2')

        left = mk_atomic_node_if_needed(node_list[1])
        right = mk_atomic_node_if_needed(node_list[2])
        type = ASTNodeType[node_name_tk.type.name]

        return ASTBinaryNode(type, left, right)
    elif node_name_tk.type == TokenType.IDENTIF and node_name_tk.contents in keywords:
        node = node_name_tk.contents
        expected_list_size = keywords[node]

        if not len(node_list) == expected_list_size:
            actual_children_count = len(node_list) - 1
            raise ASTBuildingException(
                f'{node} has not the valid number of children: {actual_children_count}/{expected_list_size}'
            )

        if expected_list_size == 2:
            return ASTUnaryNode(
                ASTNodeType[node],
                node_list[1]
            )
        elif expected_list_size == 3:
            return ASTBinaryNode(
                ASTNodeType[node],
                node_list[1],
                node_list[2]
            )
        else:
            return ASTNaryNode(
                ASTNodeType[node],
                node_list[1:]
            )


    else:
        # We didn't match the node name with anything -- that means
        # we are probably dealing with either ((X Int) (Y Int)) or (X Int)
        if len(node_list) == 2:
            return make_ast_for_type_binding(node_list)
        else:
            return make_ast_for_list(node_list)


def reduce_stack(stack: List[Any]):
    '''Reduces the stack into an ast node.'''
    current_stack_top = stack[-1]
    node_contents = []
    while not current_stack_top.type == TokenType.L_PAREN:
        node_part = stack.pop(-1)
        node_contents.append(node_part)

        current_stack_top = stack[-1]

    stack.pop(-1)
    node_contents = list(reversed(node_contents))
    return make_ast_node_from_list(node_contents)


def build_ast_from_tokens(tokens: List[Token]) -> ASTNode:
    '''Builds the AST from provided tokens, might fail, when the token stream is not valid.'''

    stack: List[Any] = []
    top_level_statements = []
    depth = 0
    for token in tokens:
        if token.type == TokenType.L_PAREN:
            depth += 1
            stack.append(token)
        elif token.type == TokenType.R_PAREN:
            if depth > 0:
                # There is at least one node list being filled right now
                node = reduce_stack(stack)
                depth -= 1

                # We might have constructed tree for whole top level statement
                if depth == 0:
                    top_level_statements.append(node)
                else:
                    # Otherwise, we are still somewhere down the tree
                    stack.append(node)
            else:
                raise ASTBuildingException('Unbalanced parenthesis')
        else:
            stack.append(token)
    return top_level_statements
