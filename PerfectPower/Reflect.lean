import PerfectPower.Certificates

namespace PerfectPower.Reflect

open PerfectPower

/-! ### A verified checker for interval-sandwich certificates (proof by reflection)

`Generated/Sandwich.lean` used to restate the polynomial in every point and interval lemma and
re-prove each inequality with `norm_num`, `gcongr` and `ring`.  Here the certificate is *data*:
a list of segments covering `[1, c)` and a tail `[c, ∞)`.  The Boolean function `check` recomputes
every polynomial it needs (Taylor shifts, powers, differences) and every numeral, and
`check_sound` proves once that `check cert = true` implies the complete hit-set statement.  A
generated certificate is then a data literal plus `decide +kernel`.

Polynomials are coefficient lists, low degree first, evaluated by Horner's rule (`ev`).  For a
rigid `F` with truncated root `P / D` and `V = D^d F`, a segment certifies, for every `n` in it,

  `0 < P(n) + t`,  `(P(n) + t)^d < V(n)`,  `V(n) < (P(n) + t + 1)^d`

(then `no_hit_of_sandwich`), or records a hit `F(n) = m^d`, a non-hit `a^d < |F(n)| < (a+1)^d`, or
a negative value for even `d`.  On an interval `[a, a + w]` positivity of a polynomial `p` is
certified from its Taylor shift `p(a + k) = POS(k) - NEG(k)` by `POS(0) > NEG(w)` (`intervalPos`).
-/

/-- Polynomials with integer coefficients, low degree first. -/
abbrev Poly := List ℤ

/-- Horner evaluation. -/
def ev : Poly → ℤ → ℤ
  | [], _ => 0
  | c :: cs, x => c + x * ev cs x

/-- Sum of polynomials. -/
def padd : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: padd p q

/-- Scalar multiple. -/
def smul (c : ℤ) (p : Poly) : Poly := p.map (c * ·)

/-- Product of polynomials. -/
def pmul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => padd (smul a q) (0 :: pmul p q)

/-- Power of a polynomial. -/
def ppow (p : Poly) : ℕ → Poly
  | 0 => [1]
  | k + 1 => pmul p (ppow p k)

/-- Difference of polynomials. -/
def psub (p q : Poly) : Poly := padd p (smul (-1) q)

/-- Taylor shift: `ev (shift p a) k = ev p (a + k)`. -/
def shift (p : Poly) (a : ℤ) : Poly := p.foldr (fun c acc => padd [c] (pmul acc [a, 1])) []

@[simp] lemma ev_nil (x : ℤ) : ev [] x = 0 := rfl
@[simp] lemma ev_cons (c : ℤ) (cs : Poly) (x : ℤ) : ev (c :: cs) x = c + x * ev cs x := rfl

lemma ev_padd : ∀ (p q : Poly) (x : ℤ), ev (padd p q) x = ev p x + ev q x
  | [], q, x => by simp [padd]
  | a :: p, [], x => by simp [padd]
  | a :: p, b :: q, x => by simp only [padd, ev_cons, ev_padd p q x]; ring

lemma ev_smul (c : ℤ) : ∀ (p : Poly) (x : ℤ), ev (smul c p) x = c * ev p x
  | [], x => by simp [smul]
  | a :: p, x => by
    have := ev_smul c p x
    simp only [smul, List.map_cons, ev_cons] at this ⊢
    rw [this]; ring

lemma ev_pmul : ∀ (p q : Poly) (x : ℤ), ev (pmul p q) x = ev p x * ev q x
  | [], q, x => by simp [pmul]
  | a :: p, q, x => by
    simp only [pmul, ev_padd, ev_smul, ev_cons, ev_pmul p q x]; ring

lemma ev_ppow (p : Poly) (x : ℤ) : ∀ k, ev (ppow p k) x = ev p x ^ k
  | 0 => by simp [ppow]
  | k + 1 => by rw [ppow, ev_pmul, ev_ppow p x k, pow_succ']

lemma ev_psub (p q : Poly) (x : ℤ) : ev (psub p q) x = ev p x - ev q x := by
  rw [psub, ev_padd, ev_smul]; ring

lemma ev_shift (a : ℤ) : ∀ (p : Poly) (k : ℤ), ev (shift p a) k = ev p (a + k)
  | [], k => by simp [shift]
  | c :: cs, k => by
    have ih := ev_shift a cs k
    simp only [shift, List.foldr_cons] at ih ⊢
    rw [ev_padd, ev_pmul, ih]
    simp; ring

/-! #### Positivity on an interval and on a half-line -/

/-- Nonnegative part of the coefficients. -/
def posPart (p : Poly) : Poly := p.map (fun c => max c 0)

/-- Negated negative part of the coefficients. -/
def negPart (p : Poly) : Poly := p.map (fun c => max (-c) 0)

lemma ev_pos_sub_neg : ∀ (p : Poly) (x : ℤ), ev p x = ev (posPart p) x - ev (negPart p) x
  | [], x => by simp [posPart, negPart]
  | c :: cs, x => by
    have := ev_pos_sub_neg cs x
    simp only [posPart, negPart, List.map_cons, ev_cons] at this ⊢
    rw [this]
    rcases le_total c 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- A polynomial with nonnegative coefficients is nonnegative and monotone on `[0, ∞)`. -/
lemma ev_nonneg_mono : ∀ (p : Poly), (∀ c ∈ p, 0 ≤ c) →
    ∀ x y : ℤ, 0 ≤ x → x ≤ y → 0 ≤ ev p x ∧ ev p x ≤ ev p y
  | [], _, x, y, _, _ => by simp
  | c :: cs, h, x, y, hx, hxy => by
    have hc : 0 ≤ c := h c (by simp)
    obtain ⟨h1, h2⟩ := ev_nonneg_mono cs (fun d hd => h d (by simp [hd])) x y hx hxy
    simp only [ev_cons]
    constructor
    · positivity
    · have : x * ev cs x ≤ y * ev cs y :=
        mul_le_mul hxy h2 h1 (le_trans hx hxy)
      linarith

lemma posPart_nonneg (p : Poly) : ∀ c ∈ posPart p, 0 ≤ c := by
  intro c hc
  simp only [posPart, List.mem_map] at hc
  obtain ⟨a, -, rfl⟩ := hc
  exact le_max_right _ _

lemma negPart_nonneg (p : Poly) : ∀ c ∈ negPart p, 0 ≤ c := by
  intro c hc
  simp only [negPart, List.mem_map] at hc
  obtain ⟨a, -, rfl⟩ := hc
  exact le_max_right _ _

/-- `POS(0) > NEG(w)` test. -/
def intervalPos (p : Poly) (w : ℤ) : Bool := decide (ev (negPart p) w < ev (posPart p) 0)

/-- Tail test: no negative coefficients and a positive constant term. -/
def tailPos (p : Poly) : Bool :=
  (negPart p).all (· == 0) && decide (0 < ev (posPart p) 0)

lemma intervalPos_sound {p : Poly} {w : ℤ} (h : intervalPos p w = true) :
    ∀ k : ℤ, 0 ≤ k → k ≤ w → 0 < ev p k := by
  intro k hk hkw
  simp only [intervalPos, decide_eq_true_eq] at h
  rw [ev_pos_sub_neg]
  have hp := (ev_nonneg_mono (posPart p) (posPart_nonneg p) 0 k le_rfl hk).2
  have hn := (ev_nonneg_mono (negPart p) (negPart_nonneg p) k w hk hkw).2
  linarith

lemma ev_zero_of_all_zero : ∀ (p : Poly), (p.all (· == 0) = true) → ∀ x, ev p x = 0
  | [], _, x => rfl
  | c :: cs, h, x => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, ev_zero_of_all_zero cs h.2 x]

lemma tailPos_sound {p : Poly} (h : tailPos p = true) : ∀ k : ℤ, 0 ≤ k → 0 < ev p k := by
  intro k hk
  simp only [tailPos, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [ev_pos_sub_neg, ev_zero_of_all_zero _ h.1]
  have hp := (ev_nonneg_mono (posPart p) (posPart_nonneg p) 0 k le_rfl hk).2
  linarith

/-! #### Certificates -/

/-- A segment of the cover of `[1, c)`. -/
inductive Seg
  /-- `F(n) = m^d`: a hit. -/
  | hit (n : ℕ) (m : ℤ)
  /-- `a^d < |F(n)| < (a + 1)^d`: not a hit. -/
  | gap (n : ℕ) (a : ℤ)
  /-- `F(n) < 0` with `d` even: not a hit. -/
  | neg (n : ℕ)
  /-- Sandwich with offset `t` on every `n ∈ [lo, hi]`. -/
  | ival (lo hi : ℕ) (t : ℤ)
  deriving DecidableEq

/-- A sandwich certificate for `F(n) = m^d`. -/
structure Cert where
  /-- `F`, low degree first. -/
  F : Poly
  /-- The exponent. -/
  d : ℕ
  /-- The common denominator of the truncated root. -/
  D : ℤ
  /-- The numerator `P` of the truncated root `P / D`. -/
  P : Poly
  /-- The segments covering `[1, c)`, in order. -/
  segs : List Seg
  /-- The tail start `c`. -/
  c : ℕ
  /-- The tail offset. -/
  tc : ℤ

/-- The three polynomials of the sandwich with offset `t`. -/
def sandPolys (C : Cert) (t : ℤ) : List Poly :=
  let Pt := padd C.P [t]
  let V := smul (C.D ^ C.d) C.F
  [Pt, psub V (ppow Pt C.d), psub (ppow (padd Pt [1]) C.d) V]

/-- Check one segment. -/
def segOK (C : Cert) : Seg → Bool
  | .hit n m => ev C.F n == m ^ C.d
  | .gap n a => decide (0 ≤ a) && decide (a ^ C.d < |ev C.F n|) && decide (|ev C.F n| < (a + 1) ^ C.d)
  | .neg n => decide (Even C.d) && decide (ev C.F n < 0)
  | .ival lo hi t => decide (lo ≤ hi) &&
      (sandPolys C t).all fun p => intervalPos (shift p lo) ((hi : ℤ) - lo)

/-- First and last index of a segment. -/
def Seg.lo : Seg → ℕ
  | .hit n _ | .gap n _ | .neg n => n
  | .ival lo _ _ => lo

/-- Last index of a segment. -/
def Seg.hi : Seg → ℕ
  | .hit n _ | .gap n _ | .neg n => n
  | .ival _ hi _ => hi

/-- Walk the segments from the cursor; `some c` if they tile `[cur, c)` and all check. -/
def walk (C : Cert) : ℕ → List Seg → Option ℕ
  | cur, [] => some cur
  | cur, s :: rest => if s.lo = cur ∧ segOK C s = true then walk C (s.hi + 1) rest else none

/-- The hits recorded in the segments. -/
def hitsOf : List Seg → List ℕ
  | [] => []
  | .hit n _ :: rest => n :: hitsOf rest
  | _ :: rest => hitsOf rest

/-- The whole check. -/
def check (C : Cert) : Bool :=
  decide (0 < C.d) && decide (walk C 1 C.segs = some C.c) &&
    (sandPolys C C.tc).all fun p => tailPos (shift p C.c)

/-! #### Soundness -/

lemma not_hit_of_sand {C : Cert} {t : ℤ} {n : ℕ}
    (h : ∀ p ∈ sandPolys C t, 0 < ev p n) : ¬ IsHit C.d (ev C.F n) := by
  simp only [sandPolys, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq,
    List.not_mem_nil, or_false] at h
  obtain ⟨h0, h1, h2⟩ := h
  rw [ev_psub, ev_smul, ev_ppow] at h1
  rw [ev_psub, ev_ppow, ev_padd, ev_smul] at h2
  simp only [ev_padd, ev_cons, ev_nil, mul_zero, add_zero] at h0 h1 h2
  exact no_hit_of_sandwich (D := C.D) (a := ev C.P n + t) h0.le (by linarith) (by linarith)

lemma segOK_sound {C : Cert} {s : Seg} (hs : segOK C s = true) :
    ∀ n, s.lo ≤ n → n ≤ s.hi → (IsHit C.d (ev C.F n) ↔ n ∈ hitsOf [s]) := by
  intro n h1 h2
  cases s with
  | hit m w =>
    simp only [Seg.lo, Seg.hi] at h1 h2
    obtain rfl : n = m := le_antisymm h2 h1
    simp only [segOK, beq_iff_eq] at hs
    simp only [hitsOf, List.mem_singleton, iff_true]
    rw [hs]; exact ⟨w, rfl⟩
  | gap m a =>
    simp only [Seg.lo, Seg.hi] at h1 h2
    obtain rfl : n = m := le_antisymm h2 h1
    simp only [segOK, Bool.and_eq_true, decide_eq_true_eq] at hs
    simp only [hitsOf, List.not_mem_nil, iff_false]
    exact not_isHit_between hs.1.1 hs.1.2 hs.2
  | neg m =>
    simp only [Seg.lo, Seg.hi] at h1 h2
    obtain rfl : n = m := le_antisymm h2 h1
    simp only [segOK, Bool.and_eq_true, decide_eq_true_eq] at hs
    simp only [hitsOf, List.not_mem_nil, iff_false]
    exact not_isHit_neg hs.1 hs.2
  | ival lo hi t =>
    simp only [Seg.lo, Seg.hi] at h1 h2
    simp only [segOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
    simp only [hitsOf, List.not_mem_nil, iff_false]
    refine not_hit_of_sand (t := t) fun p hp => ?_
    have := intervalPos_sound (hs.2 p hp) ((n : ℤ) - lo) (by omega) (by omega)
    have e : (lo : ℤ) + ((n : ℤ) - lo) = n := by ring
    rwa [ev_shift, e] at this

lemma seg_lo_le_hi {C : Cert} {s : Seg} (hs : segOK C s = true) : s.lo ≤ s.hi := by
  cases s <;> simp_all [Seg.lo, Seg.hi, segOK]

/-- A successful walk moves the cursor forward, and records hits only inside `[cur, c)`. -/
lemma walk_bounds {C : Cert} :
    ∀ (segs : List Seg) (cur c : ℕ), walk C cur segs = some c →
      cur ≤ c ∧ ∀ m ∈ hitsOf segs, cur ≤ m ∧ m < c
  | [], cur, c, h => by
    simp only [walk, Option.some.injEq] at h
    subst h
    simp [hitsOf]
  | s :: rest, cur, c, h => by
    simp only [walk] at h
    split_ifs at h with hc
    obtain ⟨hlo, hok⟩ := hc
    have hle := seg_lo_le_hi hok
    obtain ⟨hc1, ih⟩ := walk_bounds rest (s.hi + 1) c h
    refine ⟨by omega, fun m hm => ?_⟩
    cases s with
    | hit k w =>
      simp only [hitsOf, List.mem_cons] at hm
      simp only [Seg.lo, Seg.hi] at hlo hc1 hle h ih
      rcases hm with rfl | hm
      · exact ⟨by omega, by omega⟩
      · have := ih m hm; omega
    | gap k a => simp only [hitsOf] at hm; have := ih m hm; omega
    | neg k => simp only [hitsOf] at hm; have := ih m hm; omega
    | ival lo hi t => simp only [hitsOf] at hm; have := ih m hm; omega

lemma walk_sound {C : Cert} :
    ∀ (segs : List Seg) (cur c : ℕ), walk C cur segs = some c →
      ∀ n, cur ≤ n → n < c → (IsHit C.d (ev C.F n) ↔ n ∈ hitsOf segs)
  | [], cur, c, h => by
    simp only [walk, Option.some.injEq] at h
    subst h
    intro n h1 h2; omega
  | s :: rest, cur, c, h => by
    have hw := h
    simp only [walk] at h
    split_ifs at h with hc
    obtain ⟨hlo, hok⟩ := hc
    have hle := seg_lo_le_hi hok
    have ih := walk_sound rest (s.hi + 1) c h
    have hb := (walk_bounds rest (s.hi + 1) c h).2
    intro n h1 h2
    have hsplit : hitsOf (s :: rest) = hitsOf [s] ++ hitsOf rest := by
      cases s <;> simp [hitsOf]
    rw [hsplit, List.mem_append]
    rcases Nat.lt_or_ge s.hi n with hn | hn
    · rw [← ih n (by omega) h2]
      have : n ∉ hitsOf [s] := by
        cases s <;> simp_all [hitsOf, Seg.hi]; omega
      tauto
    · rw [segOK_sound hok n (by omega) hn]
      have : n ∉ hitsOf rest := fun hm => by have := hb n hm; omega
      tauto

/-- **Soundness.**  If `check C = true`, then for every `n ≥ 1`, `F(n)` is a `d`-th power iff `n` is
one of the recorded hits. -/
theorem check_sound {C : Cert} (h : check C = true) :
    ∀ n : ℕ, 1 ≤ n → (IsHit C.d (ev C.F n) ↔ n ∈ hitsOf C.segs) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨-, hw⟩, htail⟩ := h
  intro n hn
  rcases Nat.lt_or_ge n C.c with h1 | h1
  · exact walk_sound C.segs 1 C.c hw n hn h1
  · have hnot : ¬ IsHit C.d (ev C.F n) := by
      refine not_hit_of_sand (t := C.tc) fun p hp => ?_
      have := tailPos_sound (htail p hp) ((n : ℤ) - C.c) (by omega)
      have e : (C.c : ℤ) + ((n : ℤ) - C.c) = n := by ring
      rwa [ev_shift, e] at this
    have : n ∉ hitsOf C.segs := fun hm => by
      have := ((walk_bounds C.segs 1 C.c hw).2 n hm).2; omega
    tauto

/-! #### Census points on Mordell curves -/

/-- Every listed `(x, y)` in a block `(k, [(x, y), …])` satisfies `y^2 = x^3 + k`. -/
def mordellOK (L : List (ℤ × List (ℤ × ℤ))) : Bool :=
  L.all fun e => e.2.all fun p => p.2 * p.2 == p.1 ^ 3 + e.1

lemma mordellOK_append (L M : List (ℤ × List (ℤ × ℤ))) :
    mordellOK (L ++ M) = (mordellOK L && mordellOK M) := by
  simp [mordellOK, List.all_append]

/-- **Soundness of the census checker.** -/
theorem mordellOK_sound {L : List (ℤ × List (ℤ × ℤ))} (h : mordellOK L = true) :
    ∀ e ∈ L, ∀ p ∈ e.2, p.2 ^ 2 = p.1 ^ 3 + e.1 := by
  intro e he p hp
  simp only [mordellOK, List.all_eq_true, beq_iff_eq] at h
  rw [sq]; exact h e he p hp

/-! #### Runge certificates

A Runge certificate decides `[1, x₀)` point by point (the same `hit`/`gap`/`neg` segments) and
handles `[x₀, ∞)` by Theorem R: with `n = x₀ + k`, the checker verifies by Taylor shift that
`P > 0`, `(T+1) P^(d-1) ∓ R' > 0` (and `P^d ∓ R' > 0` for odd `d`), where `R' = D^d F - P^d`,
so `runge_pointwise` applies; and that each `G_t = D^d F - (P + t)^d`, `|t| ≤ T`, times a
recorded sign is positive, so no `t` survives. -/

/-- A Runge certificate. -/
structure RungeCert where
  /-- `F`, low degree first. -/
  F : Poly
  /-- The exponent. -/
  d : ℕ
  /-- The common denominator of the truncated root. -/
  D : ℤ
  /-- The numerator `P` of the truncated root `P / D`. -/
  P : Poly
  /-- The threshold. -/
  x₀ : ℕ
  /-- The `t`-range. -/
  T : ℕ
  /-- Pointwise segments covering `[1, x₀)`. -/
  segs : List Seg
  /-- Signs of `G_t`, for `t = -T, …, T`. -/
  signs : List ℤ

/-- The same data seen as a sandwich certificate, to reuse `walk`. -/
def RungeCert.toCert (C : RungeCert) : Cert := ⟨C.F, C.d, C.D, C.P, C.segs, C.x₀, 0⟩

/-- `V = D^d F`. -/
def RungeCert.V (C : RungeCert) : Poly := smul (C.D ^ C.d) C.F

/-- `R' = D^d F - P^d`. -/
def RungeCert.Rp (C : RungeCert) : Poly := psub C.V (ppow C.P C.d)

/-- `(T + 1) P^(d-1)`. -/
def RungeCert.bound (C : RungeCert) : Poly := smul ((C.T : ℤ) + 1) (ppow C.P (C.d - 1))

/-- The sign recorded for `t`. -/
def RungeCert.sgn (C : RungeCert) (t : ℤ) : ℤ := C.signs.getD (t + C.T).toNat 1

/-- `G_t = D^d F - (P + t)^d`. -/
def RungeCert.G (C : RungeCert) (t : ℤ) : Poly := psub C.V (ppow (padd C.P [t]) C.d)

/-- The whole Runge check. -/
def rungeCheck (C : RungeCert) : Bool :=
  decide (2 ≤ C.d) && decide (walk C.toCert 1 C.segs = some C.x₀) &&
    tailPos (shift C.P C.x₀) &&
    tailPos (shift (psub C.bound C.Rp) C.x₀) && tailPos (shift (padd C.bound C.Rp) C.x₀) &&
    (decide (C.d % 2 = 0) ||
      (tailPos (shift (psub (ppow C.P C.d) C.Rp) C.x₀) &&
        tailPos (shift (padd (ppow C.P C.d) C.Rp) C.x₀))) &&
    (List.range (2 * C.T + 1)).all fun i =>
      tailPos (shift (smul (C.sgn ((i : ℤ) - C.T)) (C.G ((i : ℤ) - C.T))) C.x₀)

lemma tail_at {p : Poly} {x₀ n : ℕ} (h : tailPos (shift p x₀) = true) (hn : x₀ ≤ n) :
    0 < ev p n := by
  have := tailPos_sound h ((n : ℤ) - x₀) (by omega)
  have e : (x₀ : ℤ) + ((n : ℤ) - x₀) = n := by ring
  rwa [ev_shift, e] at this

/-- **Soundness of the Runge checker.** -/
theorem rungeCheck_sound {C : RungeCert} (h : rungeCheck C = true) :
    ∀ n : ℕ, 1 ≤ n → (IsHit C.d (ev C.F n) ↔ n ∈ hitsOf C.segs) := by
  simp only [rungeCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hd, hw⟩, hP⟩, hb1⟩, hb2⟩, hodd⟩, hG⟩ := h
  intro n hn
  rcases Nat.lt_or_ge n C.x₀ with h1 | h1
  · exact walk_sound (C := C.toCert) C.segs 1 C.x₀ hw n hn h1
  · have hnot : ¬ IsHit C.d (ev C.F n) := by
      intro hit
      have hp := tail_at hP h1
      have e1 := tail_at hb1 h1
      have e2 := tail_at hb2 h1
      simp only [RungeCert.bound, RungeCert.Rp, RungeCert.V, ev_psub, ev_padd, ev_smul,
        ev_ppow] at e1 e2
      have hsmall : |C.D ^ C.d * ev C.F n - ev C.P n ^ C.d| < (C.T + 1) * |ev C.P n| ^ (C.d - 1) := by
        rw [abs_of_pos hp, abs_lt]; constructor <;> linarith
      have hodd' : Odd C.d → |C.D ^ C.d * ev C.F n - ev C.P n ^ C.d| < |ev C.P n| ^ C.d := by
        intro ho
        rcases hodd with he | ⟨o1, o2⟩
        · exact absurd (Nat.even_iff.mpr he) (Nat.not_even_iff_odd.mpr ho)
        · have f1 := tail_at o1 h1
          have f2 := tail_at o2 h1
          simp only [RungeCert.Rp, RungeCert.V, ev_psub, ev_padd, ev_smul, ev_ppow] at f1 f2
          rw [abs_of_pos hp, abs_lt]; constructor <;> linarith
      obtain ⟨t, ht, heq⟩ := runge_pointwise hd hp.ne' hodd' hsmall hit
      have hi : ((t + C.T).toNat : ℕ) < 2 * C.T + 1 := by
        have := abs_le.mp ht; omega
      have hg := tail_at (hG _ hi) h1
      have ei : (((t + C.T).toNat : ℕ) : ℤ) - C.T = t := by
        have := abs_le.mp ht; omega
      rw [ei] at hg
      simp only [RungeCert.G, RungeCert.V, ev_smul, ev_psub, ev_ppow, ev_padd, ev_cons, ev_nil,
        mul_zero, add_zero] at hg
      rw [heq, sub_self, mul_zero] at hg
      exact lt_irrefl 0 hg
    have : n ∉ hitsOf C.segs := fun hm => by
      have := ((walk_bounds (C := C.toCert) C.segs 1 C.x₀ hw).2 n hm).2; omega
    tauto

end PerfectPower.Reflect
