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


def iter_commands(chunks, *, max_command_chars=1000000, max_chunk_chars=65536):
    """Yield exact command slices from bounded text chunks, without a source list.

    Quotes may straddle any chunk boundary, including the doubled quote escape.
    Top-level whitespace/comments are discarded; other top-level text is rejected.
    The live scanner storage is bounded by one command plus one input chunk.
    An error after a yielded command does not retract that earlier command.
    """
    if type(max_command_chars) is not int or max_command_chars < 1:
        raise ValueError('positive command character bound required')
    if type(max_chunk_chars) is not int or max_chunk_chars < 1:
        raise ValueError('positive chunk character bound required')
    depth, state, buffer = 0, 'normal', []
    for chunk in chunks:
        if not isinstance(chunk, str) or len(chunk) > max_chunk_chars:
            raise ValueError('text chunk exceeds character bound or has wrong type')
        for char in chunk:
            if depth:
                buffer.append(char)
                if len(buffer) > max_command_chars:
                    raise ValueError('command exceeds character bound')
            if state == 'comment':
                if char == '\n':
                    state = 'normal'
                continue
            if state == 'symbol':
                if char == '|':
                    state = 'normal'
                continue
            if state == 'string':
                if char == '"':
                    state = 'quote'
                continue
            if state == 'quote':
                if char == '"':
                    state = 'string'
                    continue
                state = 'normal'  # The previous quote closed the string.
            if char == ';':
                state = 'comment'
            elif char == '(':
                if not depth:
                    buffer.append(char)
                depth += 1
            elif char == ')':
                if not depth:
                    raise ValueError('unbalanced parentheses')
                depth -= 1
                if not depth:
                    command = ''.join(buffer)
                    buffer.clear()
                    yield command
                    del command
            elif char in ('"', '|'):
                if not depth:
                    raise ValueError('unexpected top-level quoted text')
                state = 'string' if char == '"' else 'symbol'
            elif not depth and not char.isspace():
                raise ValueError('unexpected top-level text')
    if state in ('string', 'symbol'):
        raise ValueError('unterminated string or quoted symbol')
    if depth:
        raise ValueError('unbalanced parentheses')


def file_chunks(source, chunk_chars=65536):
    """Read a text file handle in bounded chunks (the caller owns the handle)."""
    if type(chunk_chars) is not int or chunk_chars < 1:
        raise ValueError('positive chunk character bound required')
    while True:
        chunk = source.read(chunk_chars)
        if not chunk:
            return
        yield chunk
