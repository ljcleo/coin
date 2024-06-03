import Coin.ElemRank
import Coin.Thm3

open AddSubgroup Equiv Finite Fintype Function Set

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

def test (i : ℕ) : Set (G ⧸ D_chain f (i + 1)) :=
  QuotientAddGroup.mk' (D_chain f (i + 1)) '' D_chain f i

theorem zero_mem_test (i : ℕ) : 0 ∈ test f i := ⟨0, zero_mem _, map_zero _⟩

instance test_preimage_nonempty {i : ℕ} (s : test f i) :
    Nonempty (QuotientAddGroup.mk' (D_chain f (i + 1)) ⁻¹' {s.val}) := by
  rcases s.prop with ⟨x, _, h⟩; exact ⟨x, h⟩

theorem zero_le_card_test (i : ℕ) : 0 < Nat.card (test f i) :=
  Nat.card_pos_iff.mpr ⟨⟨0, zero_mem_test _ _⟩, Finite.Set.finite_image _ _⟩

noncomputable def zz_equiv (i : ℕ) : test f i ≃ Fin (Nat.card (test f i)) :=
  (equivFin (test _ _)).trans <| swap ⟨_, zero_le_card_test _ _⟩ <|
  (equivFin (test _ _)).toFun ⟨_, zero_mem_test _ _⟩

theorem zz_equiv_zero_eq_zero (i : ℕ) :
    (zz_equiv f i) ⟨0, zero_mem_test _ _⟩ = ⟨0, zero_le_card_test _ _⟩ := by
  dsimp [zz_equiv]; rw [swap_apply_right]

example {i : ℕ} {j : Fin (Nat.card (test f i))}
    (h : j ≠ ⟨0, zero_le_card_test _ _⟩) :
    (zz_equiv f i).symm j ≠ ⟨0, zero_mem_test _ _⟩ := by
  contrapose! h
  exact
    (apply_symm_apply _ _ ▸ congrArg (zz_equiv f i) h).trans <|
    zz_equiv_zero_eq_zero f i

noncomputable def t2₀ {i : ℕ} (s : test f i) : G :=
  (Classical.choice <| test_preimage_nonempty f s).val

noncomputable def t2₁ (i : ℕ) (j : Fin (Nat.card (test f i) - 1)) : G :=
  t2₀ f ((zz_equiv f i).symm ⟨j.val, Nat.lt_of_lt_pred j.prop⟩) -
  t2₀ f ((zz_equiv f i).symm ⟨j.val + 1, Nat.succ_lt_of_lt_pred j.prop⟩)

example (i : ℕ) (x : G) (h : x ∈ D_chain f i) (h' : x ≠ 0) :
    ∃ j : Fin (Nat.card (test f i) - 1), x + ∑ k in j
