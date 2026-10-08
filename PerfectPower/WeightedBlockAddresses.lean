import PerfectPower.FactorAddresses

/-! Typed rank/select for concatenated blocks with unequal cardinalities.
The emitted rank is the sum of all preceding block sizes plus the local rank.
Zero-size blocks contribute no addresses. Parsing and CRT semantics are separate.
-/
namespace PerfectPower.FactorAddresses

/-- An address chooses a nonempty block and one of its leaves. -/
def BlockAddress : List ℕ → Type
  | [] => Fin 0
  | n::ns => Fin n ⊕ BlockAddress ns

def blockEquiv : (ns : List ℕ) → BlockAddress ns ≃ Fin ns.sum
  | [] => Equiv.refl _
  | n::ns => (Equiv.sumCongr (Equiv.refl (Fin n)) (blockEquiv ns)).trans finSumFinEquiv

def blockRank {ns : List ℕ} (a : BlockAddress ns) : Fin ns.sum := blockEquiv ns a
def blockSelect (ns : List ℕ) (i : Fin ns.sum) : BlockAddress ns := (blockEquiv ns).symm i

def blockIndex : {ns : List ℕ} → BlockAddress ns → ℕ
  | [], a => Fin.elim0 a
  | _::_, Sum.inl _ => 0
  | _::_, Sum.inr a => 1+blockIndex a

def blockLocal : {ns : List ℕ} → BlockAddress ns → ℕ
  | [], a => Fin.elim0 a
  | _::_, Sum.inl i => i.val
  | _::_, Sum.inr a => blockLocal a

def blockOffset (ns : List ℕ) (i : ℕ) : ℕ := (ns.take i).sum

@[simp] theorem block_rank_select (ns : List ℕ) (i : Fin ns.sum) :
    blockRank (blockSelect ns i)=i := (blockEquiv ns).apply_symm_apply i

@[simp] theorem block_select_rank {ns : List ℕ} (a : BlockAddress ns) :
    blockSelect ns (blockRank a)=a := (blockEquiv ns).symm_apply_apply a

theorem block_rank_injective (ns : List ℕ) : Function.Injective (@blockRank ns) :=
  (blockEquiv ns).injective

theorem block_select_surjective (ns : List ℕ) : Function.Surjective (blockSelect ns) :=
  (blockEquiv ns).symm.surjective

theorem block_rank_left (n : ℕ) (ns : List ℕ) (i : Fin n) :
    (blockRank (ns := n::ns) (Sum.inl i)).val=i.val := rfl

theorem block_rank_right (n : ℕ) (ns : List ℕ) (a : BlockAddress ns) :
    (blockRank (ns := n::ns) (Sum.inr a)).val=n+(blockRank a).val := rfl

/-- Literal prefix-sum offset, for any number of unequal blocks. -/
theorem block_rank_offset {ns : List ℕ} (a : BlockAddress ns) :
    (blockRank a).val=blockOffset ns (blockIndex a)+blockLocal a := by
  induction ns with
  | nil => exact Fin.elim0 a
  | cons n ns ih =>
    cases a with
    | inl i => simp [block_rank_left,blockIndex,blockLocal,blockOffset]
    | inr a =>
      simp [block_rank_right,blockIndex,blockLocal,blockOffset,Nat.add_comm 1,
        List.take_succ_cons,ih, Nat.add_assoc]

theorem block_index_lt {ns : List ℕ} (a : BlockAddress ns) : blockIndex a<ns.length := by
  induction ns with
  | nil => exact Fin.elim0 a
  | cons n ns ih =>
    cases a with
    | inl i => simp [blockIndex]
    | inr a => simp only [blockIndex,List.length_cons]; have := ih a; omega

/-- Empty blocks are skipped: the selected local rank is always in range. -/
theorem block_local_lt {ns : List ℕ} (a : BlockAddress ns) :
    blockLocal a < ns.getD (blockIndex a) 0 := by
  induction ns with
  | nil => exact Fin.elim0 a
  | cons n ns ih =>
    cases a with
    | inl i => simp [blockLocal,blockIndex]
    | inr a => simpa only [blockLocal,blockIndex,Nat.add_comm 1,List.getD_cons_succ] using ih a

theorem block_rank_interval {ns : List ℕ} (a : BlockAddress ns) :
    blockOffset ns (blockIndex a) ≤ (blockRank a).val ∧
    (blockRank a).val < blockOffset ns (blockIndex a)+ns.getD (blockIndex a) 0 := by
  rw [block_rank_offset]
  have := block_local_lt a
  omega

theorem block_address_card (ns : List ℕ) [Fintype (BlockAddress ns)] :
    Fintype.card (BlockAddress ns)=ns.sum := by
  rw [Fintype.card_congr (blockEquiv ns), Fintype.card_fin]

/-- Certified source semantics survive rank/select across weighted offsets. -/
theorem block_source_rank_iff {ns : List ℕ} (source : BlockAddress ns → Prop)
    (i : Fin ns.sum) : source (blockSelect ns i) ↔
      ∃ a, source a ∧ blockRank a=i := by
  constructor
  · intro h; exact ⟨blockSelect ns i,h,block_rank_select ns i⟩
  · rintro ⟨a,ha,hi⟩
    rw [←hi,block_select_rank]
    exact ha

example : (blockRank (ns := [0,2,0,5])
    (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨4,by decide⟩))))).val=6 := by decide
example : blockIndex (blockSelect [0,2,0,5] ⟨6,by decide⟩)=3 := by decide
example : blockLocal (blockSelect [0,2,0,5] ⟨6,by decide⟩)=4 := by decide

end PerfectPower.FactorAddresses
