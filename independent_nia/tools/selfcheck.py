#!/usr/bin/env python3
"""Meaningful parser/recognizer safety checks; these are not independent benchmarks."""
from inspect_corpus import parse, candidates, polynomial, head

def main():
    text = '; (bad)\n(set-info :source |unbalanced ( text ;) |)\n(set-info :note "literal ; ( and ""quote""")\n(assert (= (* x x) (+ (* 2 y) 1)))'
    forms = parse(text)
    assert len(forms)==3 and head(forms[0])=='set-info'
    got = candidates(forms,{'x','y'})
    assert len(got)==1 and got[0]['coefficients_by_degree']=={'1':2,'0':1}
    for barrier in ('or','not','ite','let','=>'):
        forms = parse('(assert ('+barrier+' (= (* x x) y)))')
        assert not candidates(forms,{'x','y'}),barrier
    assert not candidates(parse('(assert (= (* x x) (+ y z)))'),{'x','y','z'})
    assert not candidates(parse('(assert (= (* x x) (+ x 1)))'),{'x'})
    assert not candidates(parse('(assert (= (* x x) (div y 2)))'),{'x','y'})
    assert candidates(parse('(assert (and (= (* x x) y) (> y 0)))'),{'x','y'})
    assert polynomial(parse('(assert (* (- y 1) (+ y 1)))')[0][1],{'y'}) == { (('y',2),):1, (): -1}
    assert not candidates(parse('(assert (= (* x x) y))'),{'x'}), 'undeclared/noninteger rhs'
    for malformed in ('(assert true', ')(assert true)', 'atom'):
        try:
            parse(malformed)
        except ValueError:
            pass
        else:
            raise AssertionError('malformed source accepted: '+malformed)
    print('PASS: lexical metadata, polynomial normalization, declarations, malformed input, and Boolean-context barriers.')

if __name__ == '__main__':
    main()
