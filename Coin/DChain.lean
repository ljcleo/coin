import Coin.DBroadcast

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

structure CloseFSubGroup where
  H : AddSubgroup G
  CF : CloseF f H

def D_chain' : ℕ → CloseFSubGroup f
  | 0 => ⟨⊤, top_CloseF f⟩
  | k + 1 => let ⟨K, _⟩ := D_chain' k; ⟨D_Subgroup f K, D_Subgroup_CloseF f K⟩

instance D_chain'_CloseF (i : ℕ) : CloseF f (D_chain' f i).H :=
  match i with
  | 0 => top_CloseF f
  | k + 1 => @D_Subgroup_CloseF _ _ f (D_chain' f k).H (D_chain'_CloseF k)

def D_chain (i : ℕ) : AddSubgroup G := (D_chain' f i).H

instance D_chain_CloseF (i : ℕ) : CloseF f (D_chain f i) := D_chain'_CloseF f i

theorem D_chain_adj_le (i : ℕ) : D_chain f (i + 1) ≤ D_chain f i :=
  D_Subgroup_le f (D_chain f i)

theorem downward_ssub {H : AddSubgroup G} (hH : H < ⊤) [hCF : CloseF f H]
    (hCD : CloseD f ⊤ H) (n : ℕ) : ∃ (K : AddSubgroup G),
    K < D_chain f n ∧ CloseF f K ∧ CloseD f (D_chain f n) K := by
  induction' n with _ ih
  · exact ⟨H, hH, hCF, hCD⟩
  rcases ih with ⟨K, hK, _, hCD'⟩
  use D_Subgroup f K, D_Subgroup_lt_of_lt_of_CloseD hCD' hK
  exact ⟨D_Subgroup_CloseF _ _, succ_CloseD hCD'⟩

theorem upward_ssub (n : ℕ)
    (
      hn : ∃ (K : AddSubgroup G),
      K < D_chain f n ∧ CloseF f K ∧ CloseD f (D_chain f n) K
    ) : ∃ (H : AddSubgroup G), H < ⊤ ∧ CloseF f H ∧ CloseD f ⊤ H := by
  induction' n with n ih
  · rcases hn with ⟨K, hK, hCF', hCD'⟩; exact ⟨K, hK, hCF', hCD'⟩
  apply ih; rcases hn with ⟨K, hK, hCF', hCD'⟩
  exact
  ⟨
    D_Supergroup f (D_chain f n) K, D_Supergroup_lt_of_lt_of_CloseD hK,
    D_Supergroup_CloseF _ (D_chain f n) _, prec_CloseD hCD'
  ⟩
