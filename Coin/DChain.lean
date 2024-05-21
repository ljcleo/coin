import Coin.Common
import Coin.CloseF
import Coin.D

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

def D_chain : ℕ → Σ H : AddSubgroup G, CloseF f H
  | 0 => ⟨⊤, top_CloseF f⟩
  | k + 1 => let x := D_chain k; let _ := x.2; ⟨D_Subgroup f x.1, D_Subgroup_CloseF f x.1⟩

instance D_chain_fst_CloseF (i : ℕ) : CloseF f (D_chain f i).1 := by
  induction' i with i ih
  · dsimp [D_chain]; exact top_CloseF f
  dsimp [D_chain]; exact D_Subgroup_CloseF f (D_chain f i).1

def D_chain' (i : ℕ) : AddSubgroup G := (D_chain f i).1

instance (i : ℕ) : CloseF f (D_chain' f i) := D_chain_fst_CloseF f i

lemma D_chain_adj (i : ℕ) : D_chain' f (i + 1) = D_Subgroup f (D_chain' f i) := by
  simp [D_chain', D_chain]; rfl

def D_chain_adj_hom (i : ℕ) : D_chain' f i →+ D_chain' f (i + 1) :=
  D_Subgroup_Hom f (D_chain' f i)

lemma D_chain_adj_le (i : ℕ) : D_chain' f (i + 1) ≤ D_chain' f i := D_Subgroup_le f (D_chain' f i)

lemma D_chain_bounded_forever (n : ℕ) (hn : D_chain' f n = D_chain' f (n + 1))
    (k : ℕ) (hk : n ≤ k) : D_chain' f k = D_chain' f (k + 1) := by
  induction' k with k ih
  · rw [← Nat.eq_zero_of_le_zero hk]; exact hn
  by_cases h : n = k + 1
  · rw [← h]; exact hn
  replace ih := ih (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hk h))
  have (n m : ℕ) (h : D_chain' f n = D_chain' f m) :
      D_chain' f (n + 1) = D_chain' f (m + 1) := by
    simp_all only [D_chain', D_chain]
    apply (D_Subgroup_cast f) at h
    assumption
  exact this _ _ ih

theorem D_chain_bounded : ∃ i : ℕ, D_chain' f i = D_chain' f (i + 1) := by
  by_contra! h
  sorry
