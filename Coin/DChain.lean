import Coin.DBroadcast

open Set

variable {G : Type*} [Fintype G] [AddCommGroup G]

section

variable (f : G ≃+ G)
variable (i : ℕ)

structure CloseFSubGroup where
  H : AddSubgroup G
  CF : CloseF f H

def D_chain' : ℕ → CloseFSubGroup f
  | 0 => ⟨⊤, top_CloseF⟩
  | k + 1 => let ⟨K, _⟩ := D_chain' k; ⟨D_Subgroup f K, D_Subgroup_CloseF⟩

def D_chain : AddSubgroup G := (D_chain' f i).H

end

instance D_chain'_CloseF (f : G ≃+ G) (i : ℕ) : CloseF f (D_chain' f i).H :=
  match i with
  | 0 => top_CloseF
  | k + 1 => @D_Subgroup_CloseF _ _ f (D_chain' f k).H (D_chain'_CloseF f k)

section

variable {f : G ≃+ G}
variable {i : ℕ}

instance : CloseF f (D_chain f i) := D_chain'_CloseF f i

noncomputable instance : Fintype (D_chain f i) := by
  induction' i with i _
  · exact fintypeUniv
  exact Fintype.ofFinite _

end

section

variable (f : G ≃+ G)

theorem D_chain_adj_le (i : ℕ) : D_chain f (i + 1) ≤ D_chain f i :=
  D_Subgroup_le f (D_chain f i)

theorem D_chain_succ_le (i j : ℕ) : D_chain f (i + j) ≤ D_chain f i := by
  induction' j with j ih
  · exact le_refl _
  exact (D_chain_adj_le _ _).trans ih

theorem D_chain_le_of_le {i j : ℕ} (h : i ≤ j) : D_chain f j ≤ D_chain f i :=
  (Nat.add_sub_cancel' h) ▸ D_chain_succ_le f i (j - i)

end

section

variable {f : G ≃+ G}
variable (n : ℕ)

theorem downward_ssub {H : AddSubgroup G} (hH : H < ⊤)
    [hCF : CloseF f H] (hCD : CloseD f ⊤ H) : ∃ (K : AddSubgroup G),
    K < D_chain f n ∧ CloseF f K ∧ CloseD f (D_chain f n) K := by
  induction' n with _ ih
  · exact ⟨_, hH, hCF, hCD⟩
  rcases ih with ⟨K, hK, _, hCD'⟩
  exact
    ⟨
      D_Subgroup f K, D_Subgroup_lt_of_lt_of_CloseD hCD' hK,
      D_Subgroup_CloseF, succ_CloseD hCD'
    ⟩

theorem upward_ssub {K : AddSubgroup G} (hK : K < D_chain f n)
    [hCF : CloseF f K] (hCD : CloseD f (D_chain f n) K) :
    ∃ (H : AddSubgroup G), H < ⊤ ∧ CloseF f H ∧ CloseD f ⊤ H := by
  induction' n with _ ih generalizing K
  · exact ⟨_, hK, hCF, hCD⟩
  exact ih (D_Supergroup_lt_of_lt_of_CloseD hK) (pred_CloseD hCD)

end
