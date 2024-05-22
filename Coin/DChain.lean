import Coin.Common
import Coin.CloseF
import Coin.D
import Coin.CloseD
import Coin.DSubgroup

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

def D_chain : ℕ → Σ H : AddSubgroup G, CloseF f H
  | 0 => ⟨⊤, top_CloseF f⟩
  | k + 1 => let ⟨K, _⟩ := D_chain k; ⟨D_Subgroup f K, D_Subgroup_CloseF f K⟩

instance D_chain_fst_CloseF (i : ℕ) : CloseF f (D_chain f i).1 := by
  induction' i with i ih
  · dsimp [D_chain]; exact top_CloseF f
  dsimp [D_chain]; exact D_Subgroup_CloseF f (D_chain f i).1

def D_chain' (i : ℕ) : AddSubgroup G := (D_chain f i).1

instance (i : ℕ) : CloseF f (D_chain' f i) := D_chain_fst_CloseF f i

lemma D_chain_zero_top : D_chain' f 0 = ⊤ := by dsimp [D_chain', D_chain]

lemma D_chain_adj (i : ℕ) :
    D_chain' f (i + 1) = D_Subgroup f (D_chain' f i) := by
  simp [D_chain', D_chain]; rfl

def D_chain_adj_hom (i : ℕ) : D_chain' f i →+ D_chain' f (i + 1) :=
  D_Subgroup_Hom f (D_chain' f i)

lemma D_chain_adj_le (i : ℕ) : D_chain' f (i + 1) ≤ D_chain' f i :=
  D_Subgroup_le f (D_chain' f i)

lemma D_chain_always_top_of_eq_top (n : ℕ) (hn : 1 ≤ n) (h : D_chain' f n = ⊤) :
    D_chain' f 1 = ⊤ := by
  induction' n with n ih
  · rw [nonpos_iff_eq_zero] at hn; exfalso; exact one_ne_zero hn
  replace hn : 0 ≤ n := by norm_num
  by_cases h' : n = 0
  · rw [h', zero_add] at h; exact h
  replace hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h'
  have := D_chain_adj_le f n
  rw [h, top_le_iff] at this; exact ih hn this

lemma subgroup_ncard_lt_ncard_of_lt {H₁ H₂ : AddSubgroup G} (h : H₁ < H₂) :
    H₁.carrier.ncard < H₂.carrier.ncard := Set.ncard_lt_ncard h (Set.toFinite _)

lemma add_le_card_of_chain_adj_ne (k : ℕ)
    (h : ∀ i < k, D_chain' f i ≠ D_chain' f (i + 1)) :
    (D_chain' f k).carrier.ncard + k ≤ Fintype.card G := by
  rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ G]
  induction' k with k ih
  · dsimp [D_chain', D_chain]; exact le_refl _
  linarith [
    ih (fun _ hi ↦ h _ (Nat.lt_succ_of_lt hi)), subgroup_ncard_lt_ncard_of_lt
    (lt_of_le_of_ne (D_chain_adj_le f k) (h k (Nat.lt_succ_self _)).symm)
  ]

theorem D_chain_bounded :
    ∃ i ≤ Fintype.card G, D_chain' f i = D_chain' f (i + 1) := by
  by_contra! h
  linarith [
    add_le_card_of_chain_adj_ne f (Fintype.card G + 1)
    (fun i hi ↦ h i (Nat.le_of_lt_succ hi))
  ]

noncomputable def D_rank : ℕ :=
  sInf { i ≤ Fintype.card G | D_chain' f i = D_chain' f (i + 1) }

lemma D_rank_zero_of_eq_top (n : ℕ) (hn : 1 ≤ n) (h : D_chain' f n = ⊤) :
    D_rank f = 0 := by
  have := (D_chain_always_top_of_eq_top f n hn h).symm
  have : D_chain' f 0 = D_chain' f 1 := by rwa [D_chain_zero_top f]
  dsimp [D_rank]; rw [Nat.sInf_eq_zero]; left
  rwa [Set.mem_setOf_eq, zero_add, and_iff_right (zero_le _)]

noncomputable def D_core : AddSubgroup G := D_chain' f (D_rank f)

lemma D_rank_zero_of_core_top (h : D_core f = ⊤) : D_rank f = 0 := by
  dsimp [D_core] at h
  by_cases h' : D_rank f = 0
  · exact h'
  replace h' : 1 ≤ D_rank f := Nat.pos_of_ne_zero h'
  exact D_rank_zero_of_eq_top f _ h' h

lemma D_eq_of_core_top (h : D_core f = ⊤) : D_Subgroup f ⊤ = ⊤ := by
  have : D_rank f = 0 := D_rank_zero_of_core_top f h
  dsimp [D_rank] at this;
  rw [Nat.sInf_eq_zero, Set.mem_setOf_eq, zero_add] at this
  rcases this with ⟨_, h₂⟩ | h'
  · rw [D_chain_zero_top f] at h₂; dsimp [D_chain', D_chain] at h₂
    exact h₂.symm
  rcases D_chain_bounded f with ⟨x, hx⟩
  rw [Set.eq_empty_iff_forall_not_mem] at h'
  exfalso; replace h' := h' x; rw [Set.mem_setOf_eq] at h'; exact h' hx

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
    apply (D_Subgroup_cast f) at h; assumption
  exact this _ _ ih
