import Std

namespace PerfectPower.PlannerTransport

def run {S : Type} (step : S → Bool → S) (s : S) : List Bool → S
  | [] => s
  | a :: w => run step (step s a) w

theorem run_transport {S T : Type} (step : S → Bool → S) (target : T → Bool → T)
    (q : S → T) (h : ∀ s a, q (step s a) = target (q s) a) (s : S) (w : List Bool) :
    q (run step s w) = run target (q s) w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simp only [run, ih, h]

def step (s : Fin 4) (take : Bool) : Fin 4 :=
  if take then if s = 0 then 1 else if s = 1 then 0 else if s = 2 then 3 else 2 else s

def q (s : Fin 4) : Fin 2 := if s = 0 ∨ s = 2 then 0 else 1

def target (s : Fin 2) (take : Bool) : Fin 2 := if take then if s = 0 then 1 else 0 else s

theorem transition_preserved : ∀ s a, q (step s a) = target (q s) a := by decide

theorem all_words (s : Fin 4) (w : List Bool) :
    q (run step s w) = run target (q s) w :=
  run_transport step target q transition_preserved s w

def sourcePlans (s : Fin 4) (menu : List (List Bool)) : List (List Bool) :=
  menu.filter fun w => q (run step s w) == 0

def targetPlans (s : Fin 2) (menu : List (List Bool)) : List (List Bool) :=
  menu.filter fun w => run target s w == 0

theorem same_plans (s : Fin 4) (menu : List (List Bool)) :
    sourcePlans s menu = targetPlans (q s) menu := by
  simp only [sourcePlans, targetPlans, all_words]

theorem same_count (s : Fin 4) (menu : List (List Bool)) :
    (sourcePlans s menu).length = (targetPlans (q s) menu).length := by
  rw [same_plans]

theorem same_scores {V : Type} (score : List Bool → V) (s : Fin 4)
    (menu : List (List Bool)) :
    (sourcePlans s menu).map score = (targetPlans (q s) menu).map score := by
  rw [same_plans]

#print axioms run_transport
#print axioms transition_preserved
#print axioms all_words
#print axioms same_plans
#print axioms same_count
#print axioms same_scores
end PerfectPower.PlannerTransport
