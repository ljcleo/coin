import Coin.Thm4
import Coin.Thm5

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

theorem final_thm_1 : isAttackWin f ↔ D_core f = ⊥ := ⟨thm_3, thm_4⟩

theorem final_thm_2 :
    isAttackWin f ↔ ∀ H : AddSubgroup G, CloseD f ⊤ H → H = ⊤ :=
  (final_thm_1 _).trans
  ⟨unique_CloseD_of_D_core_bot, D_core_bot_of_unique_CloseD⟩

theorem final_thm_3 :
    isAttackWin f ↔ ∀ x : G, ∃ n : ℕ, (D f)^[n] x = 0 :=
  (final_thm_1 _).trans (thm_5 _)
