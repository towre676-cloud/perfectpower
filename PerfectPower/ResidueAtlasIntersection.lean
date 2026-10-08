import PerfectPower.ResidueAtlasCRT

/-! Shared-factor atlas intersections are fiber products, not Cartesian products.
The CRT reconstruction is supplied with its two projections and recovery law;
these theorems prove exact membership and cardinality for any such reconstruction.
-/
namespace PerfectPower.ResidueAtlasIntersection

def compatible (g : ℤ) (z w : ℤ × ℤ) : Prop :=
  z.1 % g = w.1 % g ∧ z.2 % g = w.2 % g

instance (g : ℤ) (z w : ℤ × ℤ) : Decidable (compatible g z w) :=
  inferInstanceAs (Decidable (_ ∧ _))

def fiberPairs (left right : Finset (ℤ × ℤ)) (g : ℤ) :=
  (left.product right).filter fun zw => compatible g zw.1 zw.2

def joined (left right : Finset (ℤ × ℤ)) (g : ℤ)
    (lift : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ)) :=
  (fiberPairs left right g).image fun zw => lift zw.1 zw.2

theorem joined_card (left right : Finset (ℤ × ℤ)) (g : ℤ)
    (lift : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ))
    (pl pr : (ℤ × ℤ) → (ℤ × ℤ))
    (hl : ∀ z w, (z,w) ∈ fiberPairs left right g → pl (lift z w) = z)
    (hr : ∀ z w, (z,w) ∈ fiberPairs left right g → pr (lift z w) = w) :
    (joined left right g lift).card = (fiberPairs left right g).card := by
  apply Finset.card_image_of_injOn
  intro zw hz tw ht he
  apply Prod.ext
  · have hh := congrArg pl he
    simpa only [hl zw.1 zw.2 hz, hl tw.1 tw.2 ht] using hh
  · have hh := congrArg pr he
    simpa only [hr zw.1 zw.2 hz, hr tw.1 tw.2 ht] using hh

theorem joined_complete (left right : Finset (ℤ × ℤ)) (g : ℤ)
    (lift : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ))
    (pl pr : (ℤ × ℤ) → (ℤ × ℤ)) (q : ℤ × ℤ)
    (hl : ∀ z w, (z,w) ∈ fiberPairs left right g → pl (lift z w) = z)
    (hr : ∀ z w, (z,w) ∈ fiberPairs left right g → pr (lift z w) = w)
    (recover : lift (pl q) (pr q) = q) :
    q ∈ joined left right g lift ↔
      pl q ∈ left ∧ pr q ∈ right ∧ compatible g (pl q) (pr q) := by
  constructor
  · intro hq
    obtain ⟨⟨z,w⟩,hz,rfl⟩ := Finset.mem_image.mp hq
    rw [hl z w hz, hr z w hz]
    have hp := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
    exact ⟨hp.1,hp.2,(Finset.mem_filter.mp hz).2⟩
  · rintro ⟨hlq,hrq,hcq⟩
    apply Finset.mem_image.mpr
    exact ⟨(pl q,pr q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hlq,hrq⟩,hcq⟩,recover⟩

/-- Bezout reconstruction before canonical reduction, for m=g*M and n=g*N.
Compatibility means b=a+g*t; u*M+v*N=1 supplies the divided inverse. -/
theorem shared_factor_reconstruction (g M N u v a t : ℤ)
    (h : u*M+v*N=1) :
    Int.ModEq (g*M) (a+g*M*u*t) a ∧
    Int.ModEq (g*N) (a+g*M*u*t) (a+g*t) := by
  constructor
  · apply Int.modEq_of_dvd
    exact ⟨-u*t, by ring⟩
  · apply Int.modEq_of_dvd
    refine ⟨v*t, ?_⟩
    calc
      (a+g*t)-(a+g*M*u*t) = g*t*(1-u*M) := by ring
      _ = (g*N)*(v*t) := by linear_combination -g*t*h

end PerfectPower.ResidueAtlasIntersection
