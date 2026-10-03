import PerfectPower.WeightedNormList

/-! A complete nonempty norm-plane list, with kernel-checked slab and signed orbit bounds. -/
namespace PerfectPower.WeightedNorm107
open UnitBox UnitPremises RankOne RankOneNorm WeightedNormList

def η : Z3 := (5,-3,2)
def ε : Z3 := (1,-1,-1)
def Dη : Matrix (Fin 3) (Fin 3) ℤ := !![360,-572,908; -227,360,-572; 143,-227,360]
def Dε : Matrix (Fin 3) (Fin 3) ℤ := !![-12,-16,4; -1,-12,-16; 4,-1,-12]
instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
def c : Cert := ⟨(-396850263 / 250000000 : ℚ),(-1587401051 / 1000000000 : ℚ),(7524449 / 1000000 : ℚ),5⟩
def L : List Z3 := [(-1,-3,0),(1,3,0)]

theorem cond : condNB 0 (-4) η c 107 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slab : slabNB 0 (-4) c 107 11 L = true := by decide +kernel

theorem forward (g : Z3) (hg : g ∈ L) (n : ℕ)
    (hn : (mul 0 (-4) g (pow 0 (-4) η n)).2.2=0) : n < 3 := by
  simp only [L,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  all_goals
    apply bound_of_data (p:=3) (by norm_num) 0 (-4) η _ (by norm_num) Dη
      (by decide +kernel) ?_ n hn
    intro r hr
    interval_cases r <;> decide +kernel

theorem backward (g : Z3) (hg : g ∈ L) (n : ℕ)
    (hn : (mul 0 (-4) g (pow 0 (-4) ε n)).2.2=0) : n < 3 := by
  simp only [L,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  all_goals
    apply bound_of_data (p:=3) (by norm_num) 0 (-4) ε _ (by norm_num) Dε
      (by decide +kernel) ?_ n hn
    intro r hr
    interval_cases r <;> decide +kernel

theorem list_eq : WeightedNormList.solutions 0 (-4) 107 η ε L 3 3 =
    [(-1,-3,0),(-1,-3,0),(1,3,0),(1,3,0)] := by decide +kernel

theorem complete (w : Z3) :
    ((nrm 0 (-4) w=107 ∨ nrm 0 (-4) w= -107) ∧ w.2.2=0) ↔
      w=(-1,-3,0) ∨ w=(1,3,0) := by
  have h := complete_of_cert (η:=η) (ε:=ε) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) cond slab (by norm_num) forward backward w
  rw [list_eq] at h
  simpa using h

theorem cubic107 (u v : ℤ) : u^3+4*v^3=107 ↔ u= -1 ∧ v=3 := by
  have hn : nrm 0 (-4) (u,-v,0)=u^3+4*v^3 := by simp [nrm]; ring
  constructor
  · intro h
    have hm := (complete (u,-v,0)).mp ⟨Or.inl (by rw [hn,h]),rfl⟩
    simp only [Prod.mk.injEq] at hm
    rcases hm with ⟨hu,hv,_⟩ | ⟨hu,hv,_⟩
    · exact ⟨hu,by omega⟩
    · have hv' : v= -3 := by omega
      rw [hu,hv'] at h
      norm_num at h
  · rintro ⟨rfl,rfl⟩
    norm_num
end PerfectPower.WeightedNorm107
