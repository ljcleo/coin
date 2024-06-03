import Coin.DCore

open AddSubgroup Function Set

variable {G : Type*} [Fintype G] [AddCommGroup G]

structure isChainInf (f : G ≃+ G) (x : G) (i : ℕ) : Prop where
  mem : x ∈ D_chain f i
  succ : x ∈ D_chain f (i + 1) → i = D_rank f

theorem chain_inf_le_rank {f : G ≃+ G} {x : G} {i : ℕ} (h : isChainInf f x i) :
    i ≤ D_rank f := by
  by_contra! h'
  exact
    (ne_of_lt h').symm <| h.succ <|
    (
      Nat.add_sub_cancel' (le_of_lt h') ▸
      D_chain_add_eq_of_eq (D_rank_is_bound f).succ (i - D_rank f)
    ) ▸ h.mem

theorem le_chain_inf_of_le_rank_of_mem_chain {f : G ≃+ G} {x : G} {i j : ℕ}
    (hi : isChainInf f x i) (hj : j ≤ D_rank f) (h : x ∈ D_chain f j) :
    j ≤ i := by
  by_contra! h'
  exact
    (ne_of_lt <| lt_of_lt_of_le h' hj) <| hi.succ <|
    mem_of_subset_of_mem (D_chain_le_of_le _ (Nat.succ_le_of_lt h')) h

theorem chain_inf_exists_of_not_mem_core {f : G ≃+ G} {x : G}
    (h : x ∉ D_core f) : ∃ i, x ∈ D_chain f i ∧ x ∉ D_chain f (i + 1) := by
  contrapose! h
  have (i : ℕ) : x ∈ D_chain f i := by
    induction' i with _ ih
    · exact mem_univ _
    exact h _ ih
  exact this (D_rank f)

theorem chain_inf_exists (f : G ≃+ G) (x : G) : ∃ i, isChainInf f x i := by
  by_cases h : x ∈ D_core f
  · exact ⟨_, h, fun _ ↦ rfl⟩
  rcases chain_inf_exists_of_not_mem_core h with ⟨_, h₁, h₂⟩
  exact ⟨_, h₁, fun _ ↦ by contradiction⟩

theorem mem_chain_of_mem_core {f : G ≃+ G} {x : G} (h : x ∈ D_core f) (i : ℕ) :
    x ∈ D_chain f i := by
  induction' i with i ih
  · exact mem_univ _
  by_cases h' : i + 1 ≤ D_rank f
  · exact mem_of_subset_of_mem (D_chain_le_of_le _ h') h
  push_neg at h'
  exact
    (
      Nat.add_sub_cancel' (Nat.le_of_lt_succ h') ▸
      D_chain_add_eq_of_eq (D_rank_is_bound f).succ (i - D_rank f)
    ).symm ▸ ih

theorem inf_eq_rank_of_mem_core {f : G ≃+ G} {x : G} (h : x ∈ D_core f) {i : ℕ}
    (h' : isChainInf f x i) : i = D_rank f :=
  h'.succ <| mem_chain_of_mem_core h _

theorem chain_inf_unique {f : G ≃+ G} {x : G} {i j : ℕ} (hi : isChainInf f x i)
    (hj : isChainInf f x j) : i = j := by
  by_cases h : x ∈ D_core f
  · exact
      (inf_eq_rank_of_mem_core h hi).trans (inf_eq_rank_of_mem_core h hj).symm
  contrapose! h
  wlog h'' : i < j generalizing i j
  · push_neg at h''; exact this hj hi h.symm <| lt_of_le_of_ne h'' h.symm
  have :=
    (
      hi.succ <|
      mem_of_subset_of_mem (D_chain_le_of_le _ <| Nat.succ_le_of_lt h'') hj.mem
    ) ▸ hi.mem
  exact this

theorem chain_inf_exists_unique (f : G ≃+ G) (x : G) :
    ∃! i, isChainInf f x i := by
  rcases chain_inf_exists f x with ⟨_, hi⟩
  exact ExistsUnique.intro _ hi fun _ hj ↦ (chain_inf_unique hi hj).symm
