import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! All-index finite-binomial-sum theorems. No Python identity is a premise. -/
namespace PerfectPower.CertifiedTelescoping
open scoped BigOperators

def B (n k : ℕ) : ℚ := n.choose k

def S (p n : ℕ) : ℚ := ∑ k ∈ Finset.range (n+1), B n k ^ p

lemma choose_step (n k : ℕ) :
    ((k:ℚ)+1) * B n (k+1) = ((n:ℚ)-k) * B n k := by
  have h := Nat.choose_succ_right_eq n k
  by_cases hk : k ≤ n
  · have hc := congrArg (fun x : ℕ => (x:ℚ)) h
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk] at hc
    simpa only [B, mul_comm] using hc
  · have h0 := Nat.choose_eq_zero_of_lt (show n < k by omega)
    have h1 := Nat.choose_eq_zero_of_lt (show n < k+1 by omega)
    simp [B, h0, h1]

lemma choose_up (n k : ℕ) :
    B n k = (((n:ℚ)+1-k)/((n:ℚ)+1)) * B (n+1) k := by
  have hn : (n:ℚ)+1 ≠ 0 := by positivity
  have h := Nat.choose_mul_succ_eq n k
  by_cases hk : k ≤ n+1
  · have hc : B n k * ((n:ℚ)+1) = B (n+1) k * ((n:ℚ)+1-k) := by
      unfold B
      rw [← Nat.cast_add_one, ← Nat.cast_sub hk]
      exact_mod_cast h
    apply (mul_right_cancel₀ hn)
    field_simp
    nlinarith [hc]
  · have h0 := Nat.choose_eq_zero_of_lt (show n < k by omega)
    have h1 := Nat.choose_eq_zero_of_lt (show n+1 < k by omega)
    simp [B,h0,h1]

lemma telescope (g : ℕ → ℚ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (g (k+1)-g k)) = g N-g 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih]; ring

lemma sum_extend (p n r : ℕ) (hp : 0 < p) :
    (∑ k ∈ Finset.range (n+r+1), B n k ^ p) = S p n := by
  induction r with
  | zero => simp [S]
  | succ r ih =>
    rw [show n+(r+1)+1 = (n+r+1)+1 by omega, Finset.sum_range_succ,ih]
    have hz := Nat.choose_eq_zero_of_lt (show n < n+r+1 by omega)
    simp [B,hz,Nat.ne_of_gt hp]

/-- A polynomial certificate in k has no endpoint pole. -/
def G (p N : ℕ) (b : ℚ → ℚ) (k : ℕ) : ℚ := (k:ℚ)^p * b k * B N k^p

lemma G_difference (p N k : ℕ) (b : ℚ → ℚ) :
    G p N b (k+1)-G p N b k =
      (((N:ℚ)-k)^p*b ((k:ℚ)+1)-(k:ℚ)^p*b k)*B N k^p := by
  have hc := congrArg (fun x : ℚ => x^p) (choose_step N k)
  simp only [mul_pow] at hc
  simp only [G, Nat.cast_add, Nat.cast_one]
  rw [show (((k:ℚ)+1)^p * b ((k:ℚ)+1) * B N (k+1)^p) =
    b ((k:ℚ)+1) * (((k:ℚ)+1)^p * B N (k+1)^p) by ring, hc]
  ring

lemma G_boundaries (p N : ℕ) (b : ℚ → ℚ) (hp : 0 < p) :
    G p N b 0 = 0 ∧ G p N b (N+1) = 0 := by
  have hz := Nat.choose_eq_zero_of_lt (show N < N+1 by omega)
  simp [G,B,hz,Nat.ne_of_gt hp]

def b2 (n k : ℚ) := (2*k-3*n-3)/(n+1)^2

def b3 (n k : ℚ) :=
  (4*k^3+(-18*n-30)*k^2+(27*n^2+93*n+78)*k
    -14*n^3-74*n^2-128*n-72)/((n+1)*(n+2)^3)

def b4 (n k : ℚ) :=
  ((16*n+20)*k^5+(-104*n^2-298*n-210)*k^4
    +(276*n^3+1244*n^2+1844*n+900)*k^3
    +(-374*n^4-2314*n^3-5298*n^2-5322*n-1980)*k^2
    +(260*n^5+2056*n^4+6420*n^3+9892*n^2+7520*n+2256)*k
    -75*n^6-725*n^5-2885*n^4-6045*n^3-7030*n^2-4300*n-1080)
    /((n+1)^3*(n+2)^4)

lemma interior2 (n k : ℕ) :
    ((n:ℚ)+1)*B (n+1) k^2-2*(2*(n:ℚ)+1)*B n k^2 =
      G 2 (n+1) (b2 n) (k+1)-G 2 (n+1) (b2 n) k := by
  rw [G_difference,choose_up n k]
  simp only [b2,Nat.cast_add,Nat.cast_one]
  have hn : (n:ℚ)+1 ≠ 0 := by positivity
  field_simp
  ring

lemma interior3 (n k : ℕ) :
    ((n:ℚ)+2)^2*B (n+2) k^3-(7*(n:ℚ)^2+21*n+16)*B (n+1) k^3
      -8*((n:ℚ)+1)^2*B n k^3 =
      G 3 (n+2) (b3 n) (k+1)-G 3 (n+2) (b3 n) k := by
  rw [G_difference,choose_up n k,choose_up (n+1) k]
  simp only [b3,Nat.cast_add,Nat.cast_one, Nat.cast_ofNat]
  have hn : (n:ℚ)+1 ≠ 0 := by positivity
  have hm : (n:ℚ)+1+1 ≠ 0 := by positivity
  have h2 : (n:ℚ)+2 ≠ 0 := by positivity
  field_simp
  ring

lemma interior4 (n k : ℕ) :
    ((n:ℚ)+2)^3*B (n+2) k^4
      -2*(2*(n:ℚ)+3)*(3*(n:ℚ)^2+9*n+7)*B (n+1) k^4
      -4*((n:ℚ)+1)*(4*(n:ℚ)+3)*(4*(n:ℚ)+5)*B n k^4 =
      G 4 (n+2) (b4 n) (k+1)-G 4 (n+2) (b4 n) k := by
  rw [G_difference,choose_up n k,choose_up (n+1) k]
  simp only [b4,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  have hn : (n:ℚ)+1 ≠ 0 := by positivity
  have hm : (n:ℚ)+1+1 ≠ 0 := by positivity
  have h2 : (n:ℚ)+2 ≠ 0 := by positivity
  field_simp
  ring

/-- The source definition is the actual finite binomial sum. -/
theorem recurrence2 (n : ℕ) :
    ((n:ℚ)+1)*S 2 (n+1) = 2*(2*(n:ℚ)+1)*S 2 n := by
  have h := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range (n+2)) => interior2 n k)
  rw [telescope, (G_boundaries 2 (n+1) (b2 n) (by omega)).1,
    (G_boundaries 2 (n+1) (b2 n) (by omega)).2] at h
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at h
  rw [show n+2 = (n+1)+0+1 by omega, sum_extend 2 (n+1) 0 (by omega),
    sum_extend 2 n 1 (by omega)] at h
  linarith

theorem recurrence3 (n : ℕ) :
    ((n:ℚ)+2)^2*S 3 (n+2) =
      (7*(n:ℚ)^2+21*n+16)*S 3 (n+1)+8*((n:ℚ)+1)^2*S 3 n := by
  have h := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range (n+3)) => interior3 n k)
  rw [telescope, (G_boundaries 3 (n+2) (b3 n) (by omega)).1,
    (G_boundaries 3 (n+2) (b3 n) (by omega)).2] at h
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at h
  simp only [sub_self] at h
  have h0 := sum_extend 3 n 2 (by omega)
  have h1 := sum_extend 3 (n+1) 1 (by omega)
  have h2 := sum_extend 3 (n+2) 0 (by omega)
  simp only [Nat.add_zero] at h2
  have he : n+1+1+1 = n+3 := by omega
  rw [he] at h1
  rw [h0,h1,h2] at h
  linarith

theorem recurrence4 (n : ℕ) :
    ((n:ℚ)+2)^3*S 4 (n+2) =
      2*(2*(n:ℚ)+3)*(3*(n:ℚ)^2+9*n+7)*S 4 (n+1)
      +4*((n:ℚ)+1)*(4*(n:ℚ)+3)*(4*(n:ℚ)+5)*S 4 n := by
  have h := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range (n+3)) => interior4 n k)
  rw [telescope, (G_boundaries 4 (n+2) (b4 n) (by omega)).1,
    (G_boundaries 4 (n+2) (b4 n) (by omega)).2] at h
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at h
  have h0 := sum_extend 4 n 2 (by omega)
  have h1 := sum_extend 4 (n+1) 1 (by omega)
  have h2 := sum_extend 4 (n+2) 0 (by omega)
  simp only [Nat.add_zero] at h2
  have he : n+1+1+1 = n+3 := by omega
  rw [he] at h1
  rw [h0,h1,h2] at h
  linarith

theorem first_power (n : ℕ) : S 1 n = (2:ℚ)^n := by
  simp only [S,pow_one,B]
  exact_mod_cast Nat.sum_range_choose n

/-- Unique order-two solution; the leading coefficient is never zero. -/
theorem second_order_unique (c d e : ℕ → ℚ) (a b : ℕ → ℚ)
    (hc : ∀ n, c n ≠ 0)
    (ha : ∀ n, c n*a (n+2)=d n*a (n+1)+e n*a n)
    (hb : ∀ n, c n*b (n+2)=d n*b (n+1)+e n*b n)
    (h0 : a 0=b 0) (h1 : a 1=b 1) : a=b := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | n
    · exact h0
    · exact h1
    · apply mul_left_cancel₀ (hc n)
      rw [ha,hb,ih (n+1) (by omega),ih n (by omega)]

/-- Executable two-state recurrence, with exact rational division. -/
def pair3 : ℕ → ℚ × ℚ
  | 0 => (1,2)
  | n+1 => let v:=pair3 n
    (v.2,((7*(n:ℚ)^2+21*n+16)*v.2+8*((n:ℚ)+1)^2*v.1)/((n:ℚ)+2)^2)

def pair4 : ℕ → ℚ × ℚ
  | 0 => (1,2)
  | n+1 => let v:=pair4 n
    (v.2,(2*(2*(n:ℚ)+3)*(3*(n:ℚ)^2+9*n+7)*v.2
      +4*((n:ℚ)+1)*(4*(n:ℚ)+3)*(4*(n:ℚ)+5)*v.1)/((n:ℚ)+2)^3)

theorem pair3_correct (n : ℕ) : pair3 n=(S 3 n,S 3 (n+1)) := by
  induction n with
  | zero => norm_num [pair3,S,B,Finset.sum_range_succ,Nat.choose]
  | succ n ih =>
    simp only [pair3,ih]
    apply Prod.ext
    · rfl
    · have hc : ((n:ℚ)+2)^2 ≠ 0 := by positivity
      apply (div_eq_iff hc).mpr
      have h := recurrence3 n
      convert h.symm using 1; ring

theorem pair4_correct (n : ℕ) : pair4 n=(S 4 n,S 4 (n+1)) := by
  induction n with
  | zero => norm_num [pair4,S,B,Finset.sum_range_succ,Nat.choose]
  | succ n ih =>
    simp only [pair4,ih]
    apply Prod.ext
    · rfl
    · have hc : ((n:ℚ)+2)^3 ≠ 0 := by positivity
      apply (div_eq_iff hc).mpr
      have h := recurrence4 n
      convert h.symm using 1; ring

/-- A rational shift identity yields a finite sum with both endpoints retained. -/
theorem antidifference_sum (ratio certificate term : ℕ → ℚ) (start length : ℕ)
    (hstep : ∀ k, term (k+1)=ratio k*term k)
    (hid : ∀ k, ratio k*certificate (k+1)-certificate k=1) :
    (∑ k ∈ Finset.range length, term (start+k)) =
      certificate (start+length)*term (start+length)-certificate start*term start := by
  have hint : ∀ k, term k=certificate (k+1)*term (k+1)-certificate k*term k := by
    intro k
    rw [hstep]
    calc
      term k = 1*term k := by ring
      _ = (ratio k*certificate (k+1)-certificate k)*term k := by rw [hid]
      _ = certificate (k+1)*(ratio k*term k)-certificate k*term k := by ring
  calc
    (∑ k ∈ Finset.range length, term (start+k)) =
      ∑ k ∈ Finset.range length,
        (certificate (start+(k+1))*term (start+(k+1))-certificate (start+k)*term (start+k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [Nat.add_assoc] using hint (start+k)
    _ = certificate (start+length)*term (start+length)-certificate start*term start := by
      simpa using telescope (fun k => certificate (start+k)*term (start+k)) length

/-- A checked antidifference gives the geometric formula at every length. -/
theorem geometric_sum (c : ℚ) (hc : c≠1) (N : ℕ) :
    (∑ k ∈ Finset.range N, c^k)=(c^N-1)/(c-1) := by
  have hden : c-1≠0 := sub_ne_zero.mpr hc
  have hi : ∀ k : ℕ, c*(1/(c-1))-1/(c-1)=1 := by
    intro k
    field_simp
  have h := antidifference_sum (fun _ => c) (fun _ => 1/(c-1)) (fun k => c^k) 0 N
    (fun k => by dsimp; rw [pow_succ]; ring) hi
  simp only [zero_add,pow_zero,mul_one] at h
  rw [h]
  simp only [div_eq_mul_inv]
  ring

/-- The rational-telescope example is a theorem for every natural cutoff. -/
theorem inverse_product_sum (N : ℕ) :
    (∑ k ∈ Finset.range N, 1/(((k:ℚ)+1)*((k:ℚ)+2)))=(N:ℚ)/((N:ℚ)+1) := by
  have hi : ∀ k : ℕ, 1/(((k:ℚ)+1)*((k:ℚ)+2)) =
      (-1/(((k+1:ℕ):ℚ)+1))-(-1/((k:ℚ)+1)) := by
    intro k
    have h1 : (k:ℚ)+1≠0 := by positivity
    have h2 : (k:ℚ)+2≠0 := by positivity
    push_cast
    field_simp
    ring
  have h := Finset.sum_congr rfl (fun k (_ : k∈Finset.range N) => hi k)
  have ht := telescope (fun k : ℕ => -1/((k:ℚ)+1)) N
  rw [ht] at h
  rw [h]
  norm_num
  have hden : (N:ℚ)+1≠0 := by positivity
  field_simp

end PerfectPower.CertifiedTelescoping
