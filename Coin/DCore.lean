import Coin.DChain

open AddSubgroup Fintype Set

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

theorem add_le_card_of_D_chain_adj_ne {k : ℕ}
    (h : ∀ i < k, D_chain f i ≠ D_chain f (i + 1)) :
    ncard (D_chain f k : Set G) + k ≤ card G := by
  rw [← Nat.card_eq_fintype_card, ← ncard_univ G]
  induction' k with n ih
  · exact le_refl _
  have h' := lt_of_le_of_ne (D_chain_adj_le _ _) (h _ (Nat.lt_succ_self _)).symm
  linarith [
    ih fun _ hi ↦ h _ (Nat.lt_succ_of_lt hi), ncard_lt_ncard h' (toFinite _)
  ]

theorem D_chain_bounded : ∃ i ≤ card G, D_chain f i = D_chain f (i + 1) := by
  by_contra! h
  linarith [
    add_le_card_of_D_chain_adj_ne f fun _ hi ↦ h _ (Nat.le_of_lt_succ hi)
  ]

noncomputable def D_rank : ℕ :=
  sInf { i ≤ card G | D_chain f i = D_chain f (i + 1) }

noncomputable def D_core : AddSubgroup G := D_chain f (D_rank f)

instance : CloseF f (D_core f) := D_chain_CloseF _ (D_rank f)

theorem D_core_eq_D_Subgroup : D_core f = D_Subgroup f (D_core f) := by
  rcases Nat.sInf_mem (D_chain_bounded f) with ⟨_, h⟩; exact h
