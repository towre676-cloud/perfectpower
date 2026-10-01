import PerfectPower.UnitPremises

/-!
# Maps between cubic orders `ℤ[t]/(t³ − Pt − Q)`

A map `R(p, q) → R(P, Q)` is fixed by the image `g` of the generator: `(a, b, c) ↦ a + b g + c g²`
(`emb`).  When `g³ = pg + q` in the target, this is a ring map.  For each concrete map the generated
module `Generated/OrderMaps.lean` proves `map_mul` and `map_nrm` by `ring`, and records the
determinant of the coordinate matrix `[1, g, g²]` (the additive index of the image).

* `OrderMap`: multiplicative and norm-preserving.  With `det ≠ 0` (checked for every generated map)
  it is an **embedding** of index `|det|` (`emb_injective`).  It carries
  source equations forward: `enc_emb` and `nrm_enc_of_map` give `N_S(c₀u − vΨ(φ)) = N_R(c₀u − vφ)`,
  so a source certificate can be built in the larger order, where unit generation may be cheaper
  or already proved.  It does **not** pull unit generation back.
* `OrderIso`: an `OrderMap` with an inverse map.  Only then does unit generation transfer:
  `unitGen_transport`.
-/

namespace PerfectPower.OrderEmbedding

open PerfectPower UnitBox UnitPremises

/-- The map sending the generator to `g`: `(a, b, c) ↦ a + b g + c g²` in `ℤ[t]`, `t³ = Pt + Q`. -/
def emb (P Q : ℤ) (g : Z3) (x : Z3) : Z3 :=
  let g2 := mul P Q g g
  (x.1 + x.2.1 * g.1 + x.2.2 * g2.1, x.2.1 * g.2.1 + x.2.2 * g2.2.1, x.2.1 * g.2.2 + x.2.2 * g2.2.2)

/-- The coordinate matrix `[1, g, g²]` as its determinant (the additive index of the image). -/
def det (P Q : ℤ) (g : Z3) : ℤ :=
  let g2 := mul P Q g g
  g.2.1 * g2.2.2 - g.2.2 * g2.2.1

/-- A multiplicative, norm-preserving map `R(p, q) → R(P, Q)`.  It is an embedding (injective, of
additive index `|det|`) exactly when `det ≠ 0` (`emb_injective`); the structure itself does not
require that: `g = 0` in `R(0, 0)` is multiplicative and norm-preserving but not injective. -/
structure OrderMap (p q P Q : ℤ) where
  /-- The image of the generator. -/
  g : Z3
  map_mul : ∀ x y : Z3, emb P Q g (mul p q x y) = mul P Q (emb P Q g x) (emb P Q g y)
  map_nrm : ∀ x : Z3, nrm P Q (emb P Q g x) = nrm p q x

/-- An `OrderMap` with an inverse `OrderMap` (index 1). -/
structure OrderIso (p q P Q : ℤ) extends OrderMap p q P Q where
  /-- The inverse map. -/
  inv : OrderMap P Q p q
  left : ∀ x : Z3, emb p q inv.g (emb P Q g x) = x
  right : ∀ y : Z3, emb P Q g (emb p q inv.g y) = y

/-- **A nonzero determinant makes the map injective.** -/
theorem emb_injective {P Q : ℤ} {g : Z3} (h : det P Q g ≠ 0) : Function.Injective (emb P Q g) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ hxy
  simp only [emb, det] at hxy h
  generalize mul P Q g g = k at hxy h
  obtain ⟨g1, g2, g3⟩ := g
  obtain ⟨k1, k2, k3⟩ := k
  simp only [Prod.mk.injEq] at hxy h ⊢
  obtain ⟨e1, e2, e3⟩ := hxy
  have hb : (g2 * k3 - g3 * k2) * (b - b') = 0 := by linear_combination k3 * e2 - k2 * e3
  have hc : (g2 * k3 - g3 * k2) * (c - c') = 0 := by linear_combination g2 * e3 - g3 * e2
  have hb' : b = b' := by
    rcases mul_eq_zero.mp hb with h0 | h0
    · exact absurd h0 h
    · linarith
  have hc' : c = c' := by
    rcases mul_eq_zero.mp hc with h0 | h0
    · exact absurd h0 h
    · linarith
  subst hb' hc'
  exact ⟨by linarith, rfl, rfl⟩

theorem emb_one (P Q : ℤ) (g : Z3) : emb P Q g (1, 0, 0) = (1, 0, 0) := by
  simp [emb]

theorem emb_neg (P Q : ℤ) (g x : Z3) : emb P Q g (neg x) = neg (emb P Q g x) := by
  simp only [emb, neg, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- **The encoding commutes with the map**: `Ψ(c₀u − vφ) = c₀u − vΨ(φ)`. -/
theorem enc_emb (P Q : ℤ) (g : Z3) (c0 : ℤ) (phi : Z3) (a b : ℤ) :
    emb P Q g (enc c0 phi a b) = enc c0 (emb P Q g phi) a b := by
  simp only [emb, enc, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- **A source norm identity moves forward**: `N_S(c₀u − vΨ(φ)) = N_R(c₀u − vφ)`. -/
theorem nrm_enc_of_map {p q P Q : ℤ} (f : OrderMap p q P Q) (c0 : ℤ) (phi : Z3) (a b : ℤ) :
    nrm P Q (enc c0 (emb P Q f.g phi) a b) = nrm p q (enc c0 phi a b) := by
  rw [← enc_emb, f.map_nrm]

theorem emb_pow {p q P Q : ℤ} (f : OrderMap p q P Q) (x : Z3) (n : ℕ) :
    emb P Q f.g (pow p q x n) = pow P Q (emb P Q f.g x) n := by
  induction n with
  | zero => simp [pow, emb_one]
  | succ n ih => simp only [pow]; rw [f.map_mul, ih]

theorem emb_zp {p q P Q : ℤ} (f : OrderMap p q P Q) (x xinv : Z3) (e : ℤ) :
    emb P Q f.g (zp p q x xinv e) = zp P Q (emb P Q f.g x) (emb P Q f.g xinv) e := by
  unfold zp
  split_ifs <;> exact emb_pow f _ _

/-- Units go to units. -/
theorem unit_map {p q P Q : ℤ} (f : OrderMap p q P Q) {u v : Z3} (h : mul p q u v = (1, 0, 0)) :
    mul P Q (emb P Q f.g u) (emb P Q f.g v) = (1, 0, 0) := by
  rw [← f.map_mul, h, emb_one]

/-- **Unit generation moves along an isomorphism**: if `ε₁, ε₂` generate the units of `R(P, Q)`,
their preimages generate the units of `R(p, q)`.  (For an embedding of index `> 1` there is no
such statement; use `nrm_enc_of_map` to move the source equation instead.) -/
theorem unitGen_transport {p q P Q : ℤ} (f : OrderIso p q P Q) {e1 e1i e2 e2i : Z3}
    (h : UnitGen P Q e1 e1i e2 e2i) :
    UnitGen p q (emb p q f.inv.g e1) (emb p q f.inv.g e1i) (emb p q f.inv.g e2)
      (emb p q f.inv.g e2i) := by
  intro u v huv
  obtain ⟨a, b, hab⟩ := h _ _ (unit_map f.toOrderMap huv)
  refine ⟨a, b, ?_⟩
  have back : ∀ w : Z3, emb P Q f.g u = w → u = emb p q f.inv.g w := by
    intro w hw; rw [← hw, f.left]
  rcases hab with hab | hab
  · left
    rw [back _ hab, f.inv.map_mul, emb_zp, emb_zp]
  · right
    rw [back _ hab, emb_neg, f.inv.map_mul, emb_zp, emb_zp]

end PerfectPower.OrderEmbedding
