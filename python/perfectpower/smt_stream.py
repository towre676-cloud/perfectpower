"""Exact SMT-LIB command slices using a token scanner implemented by Python's regex engine."""
import re

# Strings escape quotes by doubling; quoted symbols and comments hide parentheses.
# A trailing unclosed quote is an explicit error rather than a partial parse.
TOKEN = re.compile(r';[^\n]*(?:\n|$)|"(?:[^"]|"")*"|\|[^|]*\||[()]|["|]')


def split_commands_fast(source):
    commands = []
    depth = 0
    start = None
    for token in TOKEN.finditer(source):
        text = token.group()
        if text == '(':
            if depth == 0:
                start = token.start()
            depth += 1
        elif text == ')':
            depth -= 1
            if depth < 0:
                raise ValueError('unbalanced parentheses')
            if depth == 0:
                commands.append(source[start:token.end()])
        elif text in ('"', '|'):
            raise ValueError('unterminated string or quoted symbol')
    if depth:
        raise ValueError('unbalanced parentheses')
    return commands
