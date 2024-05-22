import Coin.Common
import Coin.GameDef
import Coin.CloseD
import Coin.DSubgroup
import Coin.DChain
import Coin.Thm2

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

example (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : a = c) : a = b := by linarith

lemma CloseD_iff_Subsingleton_of_core_top (hCore : D_core f = ⊤) :
    (∀ (H : AddSubgroup G) [CloseD f (@le_top _ _ _ H)], H = ⊤) ↔
    Subsingleton G := by
  constructor
  · rintro h
    have : D_Subgroup f ⊤ = ⊤ := D_eq_of_core_top f hCore
    have := (@h ⊥ (bot_CloseD_of_eq _ _ this)).symm
    rw [
      AddSubgroup.eq_bot_iff_card, AddSubgroup.card_top,
      Fintype.card_eq_one_iff
    ] at this
    rcases this with ⟨x, this⟩; exact subsingleton_of_forall_eq x this
  rw [← AddSubgroup.subsingleton_iff]; rintro ⟨h⟩ H _; exact h H ⊤

theorem thm_3_special (hCore : D_core f = ⊤) (hWin : isAttackWin f) :
    Subsingleton G := by
  rw [← CloseD_iff_Subsingleton_of_core_top f hCore]
  intro H _; exact thm_2 f H hWin
