import PerfectPower.FormulaTransport

/-! Composition laws for exact reductions. Computational receipts must still
supply each hypothesis; these laws do not certify the Python dispatcher. -/
namespace PerfectPower.ArithmeticSimplifier

/-- All integer coprime power relations, including zero and negative inputs. -/
theorem coprime_power_parameter (p q : ℕ) (_hp : p ≠ 0) (hq : q ≠ 0)
    (coprime : Nat.Coprime p q) (x y : ℤ) :
    x ^ p = y ^ q ↔ ∃ t : ℤ, x = t ^ q ∧ y = t ^ p := by
  constructor
  · intro h
    have hr : (x : ℚ) ^ p = (y : ℚ) ^ q := by exact_mod_cast h
    obtain ⟨c, hx, hy⟩ := (pow_eq_pow_iff_of_coprime coprime).mp hr
    have hden : (c ^ q).den = 1 := by rw [← hx]; simp
    rw [Rat.den_pow] at hden
    have hc : c.den = 1 := (pow_eq_one_iff hq).mp hden
    have he : c = (c.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hc).symm
    rw [he] at hx hy
    exact ⟨c.num, by exact_mod_cast hx, by exact_mod_cast hy⟩
  · rintro ⟨t, rfl, rfl⟩
    simp only [← pow_mul, Nat.mul_comm]


theorem substitute_definition {α β : Type*} (f : β → α) (C : α → β → Prop) :
    (∃ x y, x = f y ∧ C x y) ↔ ∃ y, C (f y) y := by
  constructor
  · rintro ⟨x, y, rfl, h⟩
    exact ⟨y, h⟩
  · rintro ⟨y, h⟩
    exact ⟨f y, y, rfl, h⟩

theorem parameter_context {α β : Type*} (R : α → Prop) (lift : β → α)
    (exact : ∀ x, R x ↔ ∃ t, x = lift t) (C : α → Prop) :
    (∃ x, R x ∧ C x) ↔ ∃ t, C (lift t) := by
  constructor
  · rintro ⟨x, h, hc⟩
    obtain ⟨t, rfl⟩ := (exact x).mp h
    exact ⟨t, hc⟩
  · rintro ⟨t, hc⟩
    exact ⟨lift t, (exact _).mpr ⟨t, rfl⟩, hc⟩

theorem necessary_context {α : Type*} (R N C : α → Prop)
    (necessary : ∀ x, R x → N x) :
    (∃ x, R x ∧ C x) ↔ ∃ x, R x ∧ N x ∧ C x := by
  constructor
  · rintro ⟨x, hr, hc⟩
    exact ⟨x, hr, necessary x hr, hc⟩
  · rintro ⟨x, hr, _, hc⟩
    exact ⟨x, hr, hc⟩

theorem pullback_complete {α β γ : Type*} (T : α → β) (R : β → γ → Prop)
    (L : List (β × γ)) (complete : ∀ u v, R u v ↔ (u,v) ∈ L)
    (x : α) (y : γ) :
    R (T x) y ↔ ∃ p ∈ L, T x = p.1 ∧ y = p.2 := by
  constructor
  · intro h
    exact ⟨(T x,y), (complete _ _).mp h, rfl, rfl⟩
  · rintro ⟨⟨u,v⟩, hp, hu, rfl⟩
    exact (complete _ _).mpr (by simpa only [hu] using hp)

theorem shared_outer_fibres {α β γ : Type*} (H : β → γ) (F G : α → β)
    (x y : α) : H (F x) = H (G y) ↔
    ∃ u v, F x = u ∧ G y = v ∧ H u = H v := by
  constructor
  · intro h
    exact ⟨F x, G y, rfl, rfl, h⟩
  · rintro ⟨u,v,rfl,rfl,h⟩
    exact h

theorem bounded_question {α : Type*} (R D Q : α → Prop)
    (complete : ∀ x, R x ∧ D x → Q x) :
    ∀ x, R x → D x → Q x := by
  intro x hr hd
  exact complete x ⟨hr,hd⟩

theorem global_question {α : Type*} (R N Q : α → Prop)
    (necessary : ∀ x, R x → N x) (settles : ∀ x, N x → Q x) :
    ∀ x, R x → Q x := by
  intro x hr
  exact settles x (necessary x hr)

end PerfectPower.ArithmeticSimplifier
