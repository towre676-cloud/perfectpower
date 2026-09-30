"""Reference compiler for the v14 formation invariant Theta=(S,(R_i),C).

This is deliberately finite and explicit: subgroups are stored as frozensets of
coordinate tuples.  It is intended as a theorem-side executable specification,
not as a large-group engine.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from math import gcd
from typing import Dict, FrozenSet, Iterable, Mapping, Sequence, Tuple

Elt = Tuple[int, ...]
Subgroup = FrozenSet[Elt]

@dataclass(frozen=True)
class FiniteAbelianGroup:
    moduli: Tuple[int, ...]

    def zero(self) -> Elt:
        return (0,) * len(self.moduli)

    def normalize(self, x: Sequence[int]) -> Elt:
        if len(x) != len(self.moduli):
            raise ValueError("wrong coordinate length")
        return tuple(a % n for a, n in zip(x, self.moduli))

    def add(self, x: Elt, y: Elt) -> Elt:
        return tuple((a + b) % n for a, b, n in zip(x, y, self.moduli))

    def neg(self, x: Elt) -> Elt:
        return tuple((-a) % n for a, n in zip(x, self.moduli))

    def subgroup(self, generators: Iterable[Sequence[int]]) -> Subgroup:
        gens = [self.normalize(g) for g in generators]
        seen = {self.zero()}
        frontier = [self.zero()]
        while frontier:
            x = frontier.pop()
            for g in gens:
                y = self.add(x, g)
                if y not in seen:
                    seen.add(y)
                    frontier.append(y)
        return frozenset(seen)

    def subgroup_sum(self, *subs: Subgroup) -> Subgroup:
        gens = []
        for H in subs:
            gens.extend(H)
        return self.subgroup(gens)

    def leq(self, H: Subgroup, K: Subgroup) -> bool:
        return H.issubset(K)


@dataclass(frozen=True)
class FormationState:
    """Exact invariant-level state.

    species: labels in S.
    reservoirs: R_i, represented as explicit subgroups of the supplied A_i.
    code: C, an explicit subgroup of the supplied global coinvariant group B.
    """
    species: FrozenSet[str]
    reservoirs: Mapping[str, Subgroup]
    code: Subgroup


def join(states: Sequence[FormationState],
         coefficient_groups: Mapping[str, FiniteAbelianGroup],
         coinvariant_group: FiniteAbelianGroup) -> FormationState:
    if not states:
        return FormationState(frozenset(), {}, frozenset({coinvariant_group.zero()}))
    species = frozenset().union(*(st.species for st in states))
    reservoirs: Dict[str, Subgroup] = {}
    for s in species:
        G = coefficient_groups[s]
        pieces = [st.reservoirs.get(s, frozenset({G.zero()})) for st in states]
        reservoirs[s] = G.subgroup_sum(*pieces)
    code = coinvariant_group.subgroup_sum(*(st.code for st in states))
    return FormationState(species, reservoirs, code)


def generated_membership(target: FormationState,
                         sources: Sequence[FormationState],
                         coefficient_groups: Mapping[str, FiniteAbelianGroup],
                         coinvariant_group: FiniteAbelianGroup) -> bool:
    top = join(sources, coefficient_groups, coinvariant_group)
    if not target.species.issubset(top.species):
        return False
    for s in target.species:
        G = coefficient_groups[s]
        R0 = target.reservoirs.get(s, frozenset({G.zero()}))
        R1 = top.reservoirs.get(s, frozenset({G.zero()}))
        if not G.leq(R0, R1):
            return False
    return target.code.issubset(top.code)


def cyclic_subgroup(n: int, a: int) -> FrozenSet[Tuple[int]]:
    G = FiniteAbelianGroup((n,))
    return G.subgroup([(a,)])


def cyclic_common_center_invariants(n: int, m: int):
    """One-species, M=C_n, trivial Gamma: R=C_n and C=<m>."""
    return {
        "multiplier_order": n,
        "multiplicity": m,
        "reservoir_generator": 1,
        "code_generator": m % n,
        "code_gcd": gcd(m, n),
        "canonical_state_divisor": gcd(m, n),
    }


def cyclic_canonical_contains(n: int, source_m: int, target_k: int) -> bool:
    """A_k in Form(A_m) iff <k> <= <m> iff gcd(m,n) divides k."""
    return target_k % gcd(source_m, n) == 0


def cyclic_canonical_critical(n: int, m: int) -> bool:
    """Theorem 7.2 in the v14 note, under trivial outer action."""
    def is_prime_power(q: int) -> bool:
        p = 2
        count = 0
        x = q
        while p * p <= x:
            if x % p == 0:
                count += 1
                while x % p == 0:
                    x //= p
            p += 1
        if x > 1:
            count += 1
        return count == 1
    power_of_two = n > 0 and (n & (n - 1)) == 0
    return (m == 1 and is_prime_power(n)) or (m == 2 and power_of_two)


def _self_test() -> None:
    # Join/membership on a tiny Z/4 + Z/2 example.
    A = {"a": FiniteAbelianGroup((4,)), "b": FiniteAbelianGroup((2,))}
    B = FiniteAbelianGroup((4, 2))
    z4, z2 = A["a"], A["b"]
    s1 = FormationState(
        frozenset({"a"}),
        {"a": z4.subgroup([(1,)])},
        B.subgroup([(2, 0)])
    )
    s2 = FormationState(
        frozenset({"b"}),
        {"b": z2.subgroup([(1,)])},
        B.subgroup([(0, 1)])
    )
    j = join([s1, s2], A, B)
    assert j.species == frozenset({"a", "b"})
    assert j.reservoirs["a"] == z4.subgroup([(1,)])
    assert j.reservoirs["b"] == z2.subgroup([(1,)])
    assert j.code == B.subgroup([(2, 0), (0, 1)])
    assert generated_membership(s1, [s1, s2], A, B)
    assert not generated_membership(
        FormationState(frozenset({"a"}), {"a": z4.subgroup([(1,)])}, B.subgroup([(1, 0)])),
        [s1, s2], A, B
    )
    for n in range(2, 25):
        for m in range(1, 10):
            for k in range(1, 20):
                assert cyclic_canonical_contains(n, m, k) == (k % gcd(m, n) == 0)
    print("schur_module_compiler self-test: PASS")


if __name__ == "__main__":
    _self_test()
