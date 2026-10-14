import PerfectPower.ArithmeticHeightPauli

namespace PerfectPower.ArithmeticModes
open PerfectPower.ArithmeticHeightPauli

def sign (v : Nat) (z : Int) : Int := if v%2=0 then z else -z

theorem sign_add (v : Nat) (a b : Int) : sign v (a+b)=sign v a+sign v b := by
  by_cases h : v%2=0 <;> simp [sign,h,Int.neg_add]

theorem sign_zero (v : Nat) : sign v 0=0 := by simp [sign]

def signedWord : List Bool → Int
  | [] => 1
  | true::xs => sign (xs.count false) (signedWord xs)
  | false::xs => signedWord xs

def signedBallot (p q : Nat) : Nat → Nat → Int
  | 0,0 => 1
  | u+1,0 => if p^(u+1)≤q^0 then sign 0 (signedBallot p q u 0) else 0
  | 0,v+1 => if p^0≤q^(v+1) then signedBallot p q 0 v else 0
  | u+1,v+1 => if p^(u+1)≤q^(v+1) then
      sign (v+1) (signedBallot p q u (v+1))+signedBallot p q (u+1) v else 0
termination_by u v => u+v
decreasing_by all_goals omega

theorem sum_map_up (xs : List (List Bool)) (v : Nat)
    (h : ∀ w, w∈xs → w.count false=v) :
    ((xs.map (true::·)).map signedWord).sum=sign v ((xs.map signedWord).sum) := by
  induction xs with
  | nil => simp [sign]
  | cons w xs ih =>
    have hw := h w (by simp)
    have ht : ∀ z, z∈xs → z.count false=v := fun z hz => h z (by simp [hz])
    simp only [List.map_cons,List.sum_cons,signedWord]
    rw [hw,ih ht,sign_add]

theorem sum_map_down (xs : List (List Bool)) :
    ((xs.map (false::·)).map signedWord).sum=(xs.map signedWord).sum := by
  rw [List.map_map]
  rfl

theorem sum_append_int (xs ys : List Int) : (xs++ys).sum=xs.sum+ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    change x+(xs++ys).sum=(x+xs.sum)+ys.sum
    rw [ih,Int.add_assoc]

theorem signed_enumeration (p q u v : Nat) :
    ((words p q u v).map signedWord).sum=signedBallot p q u v := by
  induction u generalizing v with
  | zero =>
    induction v with
    | zero => simp [words,signedBallot,signedWord]
    | succ v ih =>
      simp only [words,signedBallot]
      split
      · rw [sum_map_down,ih]
      · rfl
  | succ u ih =>
    induction v with
    | zero =>
      simp only [words,signedBallot]
      split
      · rw [sum_map_up _ 0 (fun w hw => good_false_count (mem_words_good p q u 0 w hw)),ih]
      · rfl
    | succ v ihv =>
      simp only [words,signedBallot]
      split
      · rw [List.map_append,sum_append_int,
          sum_map_up _ (v+1) (fun w hw => good_false_count (mem_words_good p q u (v+1) w hw)),
          sum_map_down,ih,ihv]
      · rfl

def language {S : Type} (alphabet : List Nat) (next : S → Nat → Option S)
    (accept : S → Bool) : Nat → S → List (List Nat)
  | 0,s => if accept s then [[]] else []
  | n+1,s => alphabet.flatMap (fun a =>
      (match next s a with | none => [] | some t => language alphabet next accept n t).map (a::·))

def census {S : Type} (alphabet : List Nat) (next : S → Nat → Option S)
    (accept : S → Bool) : Nat → S → Nat
  | 0,s => if accept s then 1 else 0
  | n+1,s => (alphabet.map (fun a => match next s a with
      | none => 0 | some t => census alphabet next accept n t)).sum

inductive Accepted {S : Type} (alphabet : List Nat) (next : S → Nat → Option S)
    (accept : S → Bool) : Nat → S → List Nat → Prop where
  | done {s} : accept s=true → Accepted alphabet next accept 0 s []
  | step {n s t a xs} : a∈alphabet → next s a=some t →
      Accepted alphabet next accept n t xs → Accepted alphabet next accept (n+1) s (a::xs)

theorem census_language {S : Type} (alphabet : List Nat) (next : S → Nat → Option S)
    (accept : S → Bool) (n : Nat) (s : S) :
    (language alphabet next accept n s).length=census alphabet next accept n s := by
  induction n generalizing s with
  | zero => simp only [language,census]; split <;> rfl
  | succ n ih =>
    simp only [language,census,List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro a ha
    cases he : next s a <;> simp [he,ih]

theorem accepted_mem {S : Type} {alphabet : List Nat} {next : S → Nat → Option S}
    {accept : S → Bool} {n : Nat} {s : S} {xs : List Nat}
    (h : Accepted alphabet next accept n s xs) : xs∈language alphabet next accept n s := by
  induction h with
  | done ha => simp [language,ha]
  | @step n s t a xs ha ht h ih =>
    simp only [language]
    apply List.mem_flatMap.mpr
    refine ⟨a,ha,?_⟩
    rw [ht]
    exact List.mem_map.mpr ⟨xs,ih,rfl⟩

theorem mem_accepted {S : Type} (alphabet : List Nat) (next : S → Nat → Option S)
    (accept : S → Bool) (n : Nat) (s : S) (xs : List Nat)
    (h : xs∈language alphabet next accept n s) : Accepted alphabet next accept n s xs := by
  induction n generalizing s xs with
  | zero =>
    simp only [language] at h
    split at h
    · rename_i ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      subst xs; exact Accepted.done ha
    · simp at h
  | succ n ih =>
    obtain ⟨a,ha,hx⟩ := List.mem_flatMap.mp h
    cases ht : next s a with
    | none => simp [ht] at hx
    | some t =>
      rw [ht] at hx
      obtain ⟨ys,hy,he⟩ := List.mem_map.mp hx
      subst xs; exact Accepted.step ha ht (ih t ys hy)

theorem language_complete {S : Type} (alphabet : List Nat) (next : S → Nat → Option S)
    (accept : S → Bool) (n : Nat) (s : S) (xs : List Nat) :
    xs∈language alphabet next accept n s ↔ Accepted alphabet next accept n s xs :=
  ⟨mem_accepted alphabet next accept n s xs,accepted_mem⟩

theorem accepted_length {S : Type} {alphabet : List Nat} {next : S → Nat → Option S}
    {accept : S → Bool} {n : Nat} {s : S} {xs : List Nat}
    (h : Accepted alphabet next accept n s xs) : xs.length=n := by
  induction h with
  | done => rfl
  | step ha ht h ih => simp [ih]

theorem tagged_map_nodup (a : Nat) (xs : List (List Nat)) (h : xs.Nodup) :
    (xs.map (a::·)).Nodup :=
  List.Pairwise.map _ (fun _ _ hn he => hn (List.cons.inj he).2) h

theorem tagged_flatMap_nodup (alphabet : List Nat) (f : Nat → List (List Nat))
    (ha : alphabet.Nodup) (hf : ∀ a, (f a).Nodup) :
    (alphabet.flatMap (fun a => (f a).map (a::·))).Nodup := by
  induction alphabet with
  | nil => simp
  | cons a alphabet ih =>
    have hs := List.nodup_cons.mp ha
    simp only [List.flatMap_cons]
    apply List.pairwise_append.mpr
    refine ⟨tagged_map_nodup a _ (hf a),ih hs.2,?_⟩
    intro x hx y hy
    obtain ⟨u,hu,hxu⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,hyb⟩ := List.mem_flatMap.mp hy
    obtain ⟨v,hv,hyv⟩ := List.mem_map.mp hyb
    subst x; subst y
    intro he
    have hab := (List.cons.inj he).1
    subst b; exact hs.1 hb

theorem language_nodup {S : Type} (alphabet : List Nat) (next : S → Nat → Option S)
    (accept : S → Bool) (n : Nat) (s : S) (ha : alphabet.Nodup) :
    (language alphabet next accept n s).Nodup := by
  induction n generalizing s with
  | zero => simp only [language]; split <;> simp
  | succ n ih =>
    simp only [language]
    apply tagged_flatMap_nodup _ _ ha
    intro a
    cases he : next s a <;> simp [he,ih]

theorem accepted_monotone {S : Type} {alphabet : List Nat}
    {small large : S → Nat → Option S} {a b : S → Bool}
    (hnext : ∀ s x t, small s x=some t → large s x=some t)
    (haccept : ∀ s, a s=true → b s=true)
    {n : Nat} {s : S} {xs : List Nat} (h : Accepted alphabet small a n s xs) :
    Accepted alphabet large b n s xs := by
  induction h with
  | done ha => exact Accepted.done (haccept _ ha)
  | step ha ht h ih => exact Accepted.step ha (hnext _ _ _ ht) ih

theorem language_transport {S T : Type} (alphabet : List Nat)
    (source : S → Nat → Option S) (target : T → Nat → Option T)
    (a : S → Bool) (b : T → Bool) (φ : S → T)
    (hnext : ∀ s x, target (φ s) x=(source s x).map φ)
    (haccept : ∀ s, b (φ s)=a s) (n : Nat) (s : S) :
    language alphabet target b n (φ s)=language alphabet source a n s := by
  induction n generalizing s with
  | zero => simp [language,haccept]
  | succ n ih =>
    simp only [language]
    congr 1
    funext x
    rw [hnext]
    cases he : source s x <;> simp [he,ih]

theorem census_transport {S T : Type} (alphabet : List Nat)
    (source : S → Nat → Option S) (target : T → Nat → Option T)
    (a : S → Bool) (b : T → Bool) (φ : S → T)
    (hnext : ∀ s x, target (φ s) x=(source s x).map φ)
    (haccept : ∀ s, b (φ s)=a s) (n : Nat) (s : S) :
    census alphabet target b n (φ s)=census alphabet source a n s := by
  rw [←census_language,←census_language,language_transport alphabet source target a b φ hnext haccept]

theorem weighted_transport {S T : Type} (alphabet : List Nat)
    (source : S → Nat → Option S) (target : T → Nat → Option T)
    (a : S → Bool) (b : T → Bool) (φ : S → T)
    (hnext : ∀ s x, target (φ s) x=(source s x).map φ)
    (haccept : ∀ s, b (φ s)=a s) (n : Nat) (s : S) (weight : List Nat → Int) :
    ((language alphabet target b n (φ s)).map weight).sum=
    ((language alphabet source a n s).map weight).sum := by
  rw [language_transport alphabet source target a b φ hnext haccept]


def gaussianAdd (a b : Gaussian) : Gaussian := ⟨a.re+b.re,a.im+b.im⟩
def gaussianMul (a b : Gaussian) : Gaussian := ⟨a.re*b.re-a.im*b.im,a.re*b.im+a.im*b.re⟩
def spinBasis (axis : Nat) : Bool → Bool → Gaussian
  | false,false => if axis=0 ∨ axis=3 then ⟨1,0⟩ else ⟨0,0⟩
  | true,true => if axis=0 then ⟨1,0⟩ else if axis=3 then ⟨-1,0⟩ else ⟨0,0⟩
  | false,true => if axis=1 then ⟨1,0⟩ else if axis=2 then ⟨0,-1⟩ else ⟨0,0⟩
  | true,false => if axis=1 then ⟨1,0⟩ else if axis=2 then ⟨0,1⟩ else ⟨0,0⟩
def rotate (k : Nat) (z : Gaussian) : Gaussian :=
  if k=0 then z else if k=1 then ⟨-z.im,z.re⟩ else if k=2 then ⟨-z.re,-z.im⟩ else ⟨z.im,-z.re⟩
def matrixOf (code : Nat) (s t : Bool) : Gaussian := rotate (code/4%4) (spinBasis (code%4) s t)
def matrixProduct (a b : Bool → Bool → Gaussian) (s t : Bool) : Gaussian :=
  gaussianAdd (gaussianMul (a s false) (b false t)) (gaussianMul (a s true) (b true t))
def groupTable : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [1, 0, 7, 14, 5, 4, 11, 2, 9, 8, 15, 6, 13, 12, 3, 10], [2, 15, 0, 5, 6, 3, 4, 9, 10, 7, 8, 13, 14, 11, 12, 1], [3, 6, 13, 0, 7, 10, 1, 4, 11, 14, 5, 8, 15, 2, 9, 12], [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3], [5, 4, 11, 2, 9, 8, 15, 6, 13, 12, 3, 10, 1, 0, 7, 14], [6, 3, 4, 9, 10, 7, 8, 13, 14, 11, 12, 1, 2, 15, 0, 5], [7, 10, 1, 4, 11, 14, 5, 8, 15, 2, 9, 12, 3, 6, 13, 0], [8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], [9, 8, 15, 6, 13, 12, 3, 10, 1, 0, 7, 14, 5, 4, 11, 2], [10, 7, 8, 13, 14, 11, 12, 1, 2, 15, 0, 5, 6, 3, 4, 9], [11, 14, 5, 8, 15, 2, 9, 12, 3, 6, 13, 0, 7, 10, 1, 4], [12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [13, 12, 3, 10, 1, 0, 7, 14, 5, 4, 11, 2, 9, 8, 15, 6], [14, 11, 12, 1, 2, 15, 0, 5, 6, 3, 4, 9, 10, 7, 8, 13], [15, 2, 9, 12, 3, 6, 13, 0, 7, 10, 1, 4, 11, 14, 5, 8]]
def groupProduct (a b : Nat) : Nat := (groupTable.getD a []).getD b 0

theorem group_associative : ∀ a b c : Fin 16,
    groupProduct (groupProduct a.val b.val) c.val=groupProduct a.val (groupProduct b.val c.val) := by decide
theorem group_identity : ∀ a : Fin 16, groupProduct 0 a.val=a.val ∧ groupProduct a.val 0=a.val := by decide
theorem matrix_representation : ∀ a b : Fin 16, ∀ s t : Bool,
    matrixOf (groupProduct a.val b.val) s t=matrixProduct (matrixOf a.val) (matrixOf b.val) s t := by decide
theorem pauli_anticommutation : ∀ s t : Bool,
    gaussianAdd (matrixProduct (matrixOf 1) (matrixOf 2) s t)
      (matrixProduct (matrixOf 2) (matrixOf 1) s t)=⟨0,0⟩ := by decide
theorem height_two_cancellation : ballot 2 3 2 2=2 ∧ signedBallot 2 3 2 2=0 := by
  simp only [ballot,signedBallot,sign]; decide
theorem height_three_revival : ballot 2 3 3 3=7 ∧ signedBallot 2 3 3 3=-1 := by
  simp only [ballot,signedBallot,sign]; decide

theorem square_wall_phase (p q : Nat) (hp : 1<p) (hpq : p<q) :
    ballot p q 2 2=(if p^2≤q then 3 else 2) ∧
    signedBallot p q 2 2=(if p^2≤q then 1 else 0) := by
  have hq : 1<q := by omega
  have hpq' : p≤q := by omega
  have hppqq : p^2≤q^2 := Nat.pow_le_pow_left hpq' 2
  have hpgt := Nat.pow_lt_pow_right hp (show 1<2 by decide)
  have hqgt := Nat.pow_lt_pow_right hq (show 1<2 by decide)
  simp only [Nat.pow_one] at hpgt hqgt
  have hpp : ¬p^2≤1 := by omega
  have hp1 : ¬p≤1 := by omega
  have hpqq : p≤q^2 := by omega
  have hq1 : 1≤q := by omega
  have hqq1 : 1≤q^2 := by omega
  by_cases h : p^2≤q
  · simp [ballot,signedBallot,sign,h,hppqq,hpp,hp1,hpqq,hq1,hqq1,hpq']
  · simp [ballot,signedBallot,sign,h,hppqq,hpp,hp1,hpqq,hq1,hqq1,hpq']

end PerfectPower.ArithmeticModes
