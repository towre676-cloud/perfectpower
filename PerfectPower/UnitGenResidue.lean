import PerfectPower.UnitGen
import PerfectPower.NormRepProof

/-!
# Residue-filtered unit slabs

`UnitGenProof.unitSlabSlice` tests every lattice point of the slab for norm `±1`.  Most of them
fail for local reasons.  This module checks, once per order, tables of the residues
`a mod 8` and `a mod 9` that admit `N(a, b, c) ≡ s` for each sign `s = ±1` and each `(b mod m,
c mod m)` (`tabB`, `8³ + 9³ = 1241` triples).  For a unit `(a, b, c)` of norm `s`, `a mod 72` is
then the CRT combination `9 a₈ − 8 a₉ mod 72` of two entries of the tables **for the same sign**
(`mem_mask`).  `unitResidueSlice` enumerates, in each slab row, only the first coordinates in the
allowed classes mod 72: `a₀ = L + ((r − L) mod 72)`, `a₀ + 72k`.  `reduced_of_residueSlab` gives
`UnitGenProof.Reduced`, which feeds the unchanged `UnitGenProof.unitGen_of_core`.

The masks prune only points of norm `≠ ±1`; the conclusion is the same as `unitGen_of_slab`.
The design and the Python prototype are from the CRT-slab review of `1a7fad9`.
-/

namespace PerfectPower.UnitGenResidue

open PerfectPower UnitBox UnitPremises UnitGenProof NormRepProof

/-- The entry `(b, c)` of a residue table (empty when out of range). -/
def tabGet (T : List (List (List ℕ))) (b c : ℕ) : List ℕ := (T.getD b []).getD c []

/-- Completeness of a table: every residue `a mod m` with `N(a, b, c) ≡ s (mod m)` is listed. -/
def tabB (P Q : ℤ) (m : ℕ) (s : ℤ) (T : List (List (List ℕ))) : Bool :=
  (List.range m).all fun b => (List.range m).all fun c => (List.range m).all fun a =>
    decide (nrm P Q ((a : ℤ), (b : ℤ), (c : ℤ)) % m ≠ s % m) || decide (a ∈ tabGet T b c)

/-- The norm modulo `m` depends only on the coordinates modulo `m`. -/
lemma nrm_emod (P Q x y z : ℤ) (m : ℕ) :
    nrm P Q (x % m, y % m, z % m) % m = nrm P Q (x, y, z) % m := by
  apply (ZMod.intCast_eq_intCast_iff' _ _ m).mp
  rw [nrm_cast, nrm_cast]
  simp [ZMod.intCast_mod]

lemma tab_sound {P Q : ℤ} {m : ℕ} {s : ℤ} {T : List (List (List ℕ))} (hm : 0 < m)
    (h : tabB P Q m s T = true) {x y z : ℤ} (hn : nrm P Q (x, y, z) = s) :
    (x % m).toNat ∈ tabGet T (y % m).toNat (z % m).toNat := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hx0 := Int.emod_nonneg x hm'.ne'
  have hy0 := Int.emod_nonneg y hm'.ne'
  have hz0 := Int.emod_nonneg z hm'.ne'
  have hx1 := Int.emod_lt_of_pos x hm'
  have hy1 := Int.emod_lt_of_pos y hm'
  have hz1 := Int.emod_lt_of_pos z hm'
  simp only [tabB, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h (y % m).toNat (by omega) (z % m).toNat (by omega) (x % m).toNat (by omega) with h1 | h1
  · exfalso
    apply h1
    rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0, Int.toNat_of_nonneg hz0, nrm_emod, hn]
  · exact h1

/-- The four tables of an order: residues mod 8 and mod 9, for norm `+1` and for norm `−1`. -/
structure ResTables where
  /-- mod 8, norm `+1`. -/
  p8 : List (List (List ℕ))
  /-- mod 8, norm `−1`. -/
  n8 : List (List (List ℕ))
  /-- mod 9, norm `+1`. -/
  p9 : List (List (List ℕ))
  /-- mod 9, norm `−1`. -/
  n9 : List (List (List ℕ))

/-- All four tables are complete. -/
def tablesB (P Q : ℤ) (R : ResTables) : Bool :=
  tabB P Q 8 1 R.p8 && tabB P Q 8 (-1) R.n8 && tabB P Q 9 1 R.p9 && tabB P Q 9 (-1) R.n9

/-- The CRT combinations of two table entries of the same sign. -/
def crtList (A B : List ℕ) : List ℤ :=
  A.flatMap fun (a8 : ℕ) => B.map fun (a9 : ℕ) => (9 * (a8 : ℤ) - 8 * (a9 : ℤ)) % 72

/-- The classes mod 72 allowed for a unit in the row `(b, c)`. -/
def mask (R : ResTables) (b c : ℤ) : List ℤ :=
  crtList (tabGet R.p8 (b % 8).toNat (c % 8).toNat) (tabGet R.p9 (b % 9).toNat (c % 9).toNat) ++
  crtList (tabGet R.n8 (b % 8).toNat (c % 8).toNat) (tabGet R.n9 (b % 9).toNat (c % 9).toNat)

lemma crt_mem {A B : List ℕ} {x : ℤ} (hA : (x % 8).toNat ∈ A) (hB : (x % 9).toNat ∈ B) :
    x % 72 ∈ crtList A B := by
  simp only [crtList, List.mem_flatMap, List.mem_map]
  refine ⟨(x % 8).toNat, hA, (x % 9).toNat, hB, ?_⟩
  have h8 := Int.emod_nonneg x (by norm_num : (8 : ℤ) ≠ 0)
  have h9 := Int.emod_nonneg x (by norm_num : (9 : ℤ) ≠ 0)
  rw [Int.toNat_of_nonneg h8, Int.toNat_of_nonneg h9]
  omega

/-- **The mask is complete**: a unit's first coordinate lies in an allowed class mod 72. -/
theorem mem_mask {P Q : ℤ} {R : ResTables} (h : tablesB P Q R = true) {x y z : ℤ}
    (hn : nrm P Q (x, y, z) = 1 ∨ nrm P Q (x, y, z) = -1) : x % 72 ∈ mask R y z := by
  simp only [tablesB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [mask, List.mem_append]
  rcases hn with hn | hn
  · exact Or.inl (crt_mem (tab_sound (by norm_num) h1 hn) (tab_sound (by norm_num) h3 hn))
  · exact Or.inr (crt_mem (tab_sound (by norm_num) h2 hn) (tab_sound (by norm_num) h4 hn))

/-- The first allowed coordinate `≥ L` in the class `r` mod 72. -/
def start (L r : ℤ) : ℤ := L + (r - L) % 72

/-- **The progression covers the class**: `L ≤ x ≤ H` with `x ≡ r (mod 72)` is `start L r + 72 k`
with `k < (H − start L r) / 72 + 1`. -/
lemma progression {L H r x : ℤ} (hL : L ≤ x) (hH : x ≤ H) (hr : x % 72 = r) :
    ((x - start L r) / 72).toNat < ((H - start L r) / 72 + 1).toNat ∧
      start L r + 72 * (((x - start L r) / 72).toNat : ℤ) = x := by
  simp only [start]
  omega

/-- Slice `t` (width `w`) of the residue-filtered slab: as `unitSlabSlice`, but in each row only
the classes of `mask` are enumerated, and the row bounds are computed only for nonempty masks. -/
def unitResidueSlice (P Q : ℤ) (C : UGCert) (R : ResTables) (cands : List Z3) (w t : ℕ) : Bool :=
  (List.range' (t * w) w).all fun j => !decide (j < 2 * C.bb + 1) ||
    (List.range (2 * C.bc + 1)).all fun k =>
      let b : ℤ := (j : ℤ) - C.bb
      let c : ℤ := (k : ℤ) - C.bc
      (mask R b c).all fun r =>
        let a0 := start (slabLo C b c) r
        (List.range ((slabHi C b c - a0) / 72 + 1).toNat).all fun i =>
          let g : Z3 := (a0 + 72 * i, b, c)
          !decide (nrm P Q g = 1 ∨ nrm P Q g = -1) || decide (g ∈ cands)

/-- The slices of the residue-filtered slab prove the finite step. -/
lemma reduced_of_residueSlab {P Q : ℤ} {C : UGCert} {R : ResTables} {cands : List Z3} {w n : ℕ}
    (hR : tablesB P Q R = true) (hw : 0 < w) (hn : 2 * C.bb + 1 ≤ n * w)
    (h : ∀ t < n, unitResidueSlice P Q C R cands w t = true) : Reduced P Q C cands := by
  intro t1 t2 t3 a1 a1' a2 a2' a3 a3' g hnrm u1 u2 u3 _ gb gc
  obtain ⟨hl, hh⟩ := slab_mem a1 a1' a2 a2' a3 a3' g u1 u2 u3
  obtain ⟨x, y, z⟩ := g
  simp only at hl hh gb gc hnrm
  have hm := mem_mask hR hnrm
  have gb' := abs_le.mp gb
  have gc' := abs_le.mp gc
  set j := (y + C.bb).toNat
  have hjlt : j < 2 * C.bb + 1 := by omega
  have ht : j / w < n := by rw [Nat.div_lt_iff_lt_mul hw]; omega
  have hs := h (j / w) ht
  simp only [unitResidueSlice, List.all_eq_true, List.mem_range', List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hs
  have hjm : ∃ k < w, j = j / w * w + k := ⟨j % w, Nat.mod_lt _ hw, by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod j w).symm⟩
  obtain ⟨k, hk, hjk⟩ := hjm
  rcases hs j ⟨k, hk, by simpa [Nat.mul_comm] using hjk⟩ with hlt | hrest
  · exact absurd hjlt hlt
  have ey : ((j : ℕ) : ℤ) - C.bb = y := by omega
  have hz := hrest (z + C.bc).toNat (by omega)
  have ez : (((z + C.bc).toNat : ℕ) : ℤ) - C.bc = z := by omega
  rw [ey, ez] at hz
  obtain ⟨hi1, hi2⟩ := progression hl hh rfl
  have hi := hz (x % 72) hm _ hi1
  rw [hi2] at hi
  exact hi.resolve_left (not_not.mpr hnrm)

/-- **Unit generation from a residue-filtered slab**: `ugCore`, the residue tables, and the slices. -/
theorem unitGen_of_residueSlab (P Q : ℤ) (e1 e1i e2 e2i : Z3) (C : UGCert) (R : ResTables) {w n : ℕ}
    (hcore : ugCore P Q e1 e1i e2 e2i C = true) (hR : tablesB P Q R = true) (hw : 0 < w)
    (hn : 2 * C.bb + 1 ≤ n * w)
    (h : ∀ t < n, unitResidueSlice P Q C R (C.reps.map (evalRep P Q e1 e1i e2 e2i)) w t = true) :
    UnitGen P Q e1 e1i e2 e2i :=
  unitGen_of_core P Q e1 e1i e2 e2i C hcore (reduced_of_residueSlab hR hw hn h)

end PerfectPower.UnitGenResidue
