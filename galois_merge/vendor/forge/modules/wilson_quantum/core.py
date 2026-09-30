from __future__ import annotations
import numpy as np

def commutator_coordinates(algebra,a,b):
    return algebra.multiply(a,b)-algebra.multiply(b,a)

def hermitianize(algebra,a):
    return a+algebra.adjoint(a)
