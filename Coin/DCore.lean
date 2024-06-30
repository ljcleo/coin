import Coin.DRank

open Set

variable {G : Type*} [Fintype G] [AddCommGroup G]

section

variable (f : G ≃+ G)

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

theorem D_bijOn_D_core : BijOn (D f) (D_core f) (D_core f) := by
  apply D_bijOn_of_D_image_eq; rw [D_core]
  nth_rw 2 [(D_rank_is_bound f).succ]; rfl

theorem D_ne_zero_of_mem_core_of_ne_zero {f : G ≃+ G} {x : G} (h : x ∈ D_core f)
    (h' : x ≠ 0) : D f x ≠ 0 := by
  contrapose! h'
  exact
    (D_bijOn_D_core f).injOn h (zero_mem _) <| h'.trans (map_zero (D f)).symm

end
