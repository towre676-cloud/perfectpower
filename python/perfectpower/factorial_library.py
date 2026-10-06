"""Shared nonlinear factorial-ratio sequences and huge-index residues."""
from fractions import Fraction as Q
from copy import deepcopy
from .gamma_arithmetic import hypergeometric,hypergeometric_terms,factorial_unit,landau,_natural


class FactorialLibrary:
    def __init__(self,specification):
        if set(specification)!={'families'} or not isinstance(specification['families'],dict) or not 1<=len(specification['families'])<=64:
            raise ValueError('one through 64 named factorial-ratio definitions required')
        self.specification=deepcopy(specification);self.recurrences={};self.integrality={}
        for name,definition in specification['families'].items():
            if not isinstance(name,str) or not name.isidentifier() or set(definition)!={'numerator','denominator'}:
                raise ValueError('named numerator/denominator slope families required')
            a,b=definition['numerator'],definition['denominator'];self.recurrences[name]=hypergeometric(a,b)
            self.integrality[name]=landau(a,b) if sum(a)==sum(b) else None

    def summary(self):
        return dict(names=list(self.recurrences),recurrences=self.recurrences,integrality=self.integrality,
                    scope='exact supplied factorial-ratio definitions; nonlinear polynomial-coefficient recurrences')

    def terms(self,count=16):
        return {name:hypergeometric_terms(receipt,count) for name,receipt in self.recurrences.items()}

    def residues(self,index,prime,depth=1):
        _natural(index)
        factorial_unit(0,prime,depth)  # Validate even a constant family.
        # The same stripped factorial at slope c is reused across all readouts.
        units={};results={}
        for name,receipt in self.recurrences.items():
            a,b=receipt['numerator_slopes'],receipt['denominator_slopes']
            for c in a+b:
                if c not in units:units[c]=factorial_unit(c*index,prime,depth)
            exponent=sum(units[c]['valuation'] for c in a)-sum(units[c]['valuation'] for c in b)
            modulus=prime**depth;unit=1
            for c in a:unit=unit*units[c]['unit']%modulus
            for c in b:unit=unit*pow(units[c]['unit'],-1,modulus)%modulus
            results[name]=dict(exponent=exponent,unit=unit,status='P_INTEGRAL' if exponent>=0 else 'NON_P_INTEGRAL',
                value=None if exponent<0 else 0 if exponent>=depth else unit*prime**exponent%modulus)
        return dict(schema='pp-factorial-library-residues/1',index=index,prime=prime,depth=depth,modulus=prime**depth,
            outputs=results,shared_factorial_units={str(c):r for c,r in units.items()},unique_factorials=len(units),
            scope='p-integral rational-term residues; global integer-sequence semantics use the separate integrality certificate',execution_verified=False)
