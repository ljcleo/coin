import Coin.DChain

open Fintype Set

variable {G : Type*} [Fintype G] [AddCommGroup G]

structure isDChainBound (f : G ≃+ G) (i : ℕ) : Prop where
  pred : D_chain f (i - 1) = D_chain f i → i = 0
  succ : D_chain f i = D_chain f (i + 1)

section

variable {f : G ≃+ G}

theorem D_chain_add_eq_of_eq {i : ℕ} (h : D_chain f i = D_chain f (i + 1))
    (j : ℕ) : D_chain f (i + j) = D_chain f (i + j + 1) := by
  induction' j with _ ih
  · exact h
  exact congrArg (D_Subgroup f) <| ih

theorem D_chain_bound_exists_of_top_ne_of_bounded (h : ⊤ ≠ D_Subgroup f ⊤)
    (h' : ∃ i, D_chain f i = D_chain f (i + 1)) :
    ∃ i, D_chain f (i + 1) < D_chain f i ∧
    D_chain f (i + 1) = D_chain f (i + 2) := by
  by_contra! h''
  have (i : ℕ) : D_chain f (i + 1) < D_chain f i := by
    induction' i with i ih
    · exact lt_of_le_of_ne (D_chain_adj_le f _) h.symm
    exact lt_of_le_of_ne (D_chain_adj_le f _) (h'' _ ih).symm
  rcases h' with ⟨_, hj⟩; exact ne_of_lt (this _) hj.symm

theorem D_chain_bound_exists_of_bounded
    (h : ∃ i, D_chain f i = D_chain f (i + 1)) : ∃ i, isDChainBound f i := by
  by_cases h' : ⊤ = D_Subgroup f ⊤
  · exact ⟨_, fun _ ↦ rfl, h'⟩
  rcases D_chain_bound_exists_of_top_ne_of_bounded h' h with ⟨i, h₁, h₂⟩
  exact ⟨_, fun h'' ↦ by exfalso; exact ne_of_lt h₁ h''.symm, h₂⟩

theorem D_chain_bound_unique {i j : ℕ} (hi : isDChainBound f i)
    (hj : isDChainBound f j) : i = j := by
  by_contra! h
  wlog h' : i < j generalizing i j
  · push_neg at h'; exact this hj hi h.symm <| lt_of_le_of_ne h' h.symm
  replace h : j ≠ 0 := ne_zero_of_lt h'
  exact
    h <| hj.pred <| Nat.succ_pred h ▸
    Nat.add_sub_cancel' (Nat.le_pred_of_lt h') ▸
    D_chain_add_eq_of_eq hi.succ (j - 1 - i)

end

section

variable (f : G ≃+ G)

theorem D_chain_bounded' : ∃ i, D_chain f i = D_chain f (i + 1) := by
  by_contra! h
  replace h (i : ℕ) : ncard (D_chain f i : Set G) + i ≤ card G := by
    induction' i with i ih
    · dsimp [D_chain, D_chain']
      rw [ncard_univ, Nat.card_eq_fintype_card]
    trans ncard (D_chain f i : Set G) + i
    · nth_rw 2 [add_comm i]; rw [← add_assoc, add_le_add_iff_right]
      refine Nat.succ_le_of_lt <| ncard_lt_ncard ?_ <| toFinite _
      apply lt_of_le_of_ne (D_chain_adj_le _ _)
      exact (h i).symm
    exact ih
  linarith [h (card G + 1)]

theorem D_chain_exists_unique_bound : ∃! i, isDChainBound f i := by
  rcases D_chain_bound_exists_of_bounded <| D_chain_bounded' f with ⟨_, hi⟩
  exact ExistsUnique.intro _ hi fun _ hj ↦ (D_chain_bound_unique hi hj).symm

noncomputable def D_rank_unique : Unique { a // isDChainBound f a } :=
  Classical.choice <| (unique_subtype_iff_exists_unique _).mpr <|
  D_chain_exists_unique_bound _

noncomputable def D_rank : ℕ := (D_rank_unique f).default

theorem D_rank_is_bound : isDChainBound f <| D_rank f :=
  (D_rank_unique _).toInhabited.default.property

noncomputable def D_core : AddSubgroup G := D_chain f (D_rank f)

theorem D_core_le_chain (i : ℕ) : D_core f ≤ D_chain f i := by
  induction' i with i ih
  · exact le_top
  by_cases h : i + 1 ≤ D_rank f
  · exact D_chain_le_of_le _ h
  push_neg at h
  replace h : D_rank f ≤ i := Nat.le_of_lt_succ h
  exact
    le_of_eq <| (eq_of_le_of_le ih <| D_chain_le_of_le _ h).trans <|
    Nat.add_sub_cancel' h ▸
    D_chain_add_eq_of_eq (D_rank_is_bound _).succ (i - D_rank f)

end
