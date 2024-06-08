import Coin.Thm4

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

theorem final_thm_1 : isAttackWin f ↔ D_core f = ⊥ := ⟨thm_3, thm_4⟩

theorem final_thm_2 :
    D_core f = ⊥ ↔ ∀ H : AddSubgroup G, CloseD f ⊤ H → H = ⊤ :=
  ⟨unique_CloseD_of_D_core_bot, D_core_bot_of_unique_CloseD⟩

theorem final_thm_3 :
    isAttackWin f ↔ ∀ H : AddSubgroup G, CloseD f ⊤ H → H = ⊤ :=
  (final_thm_1 _).trans (final_thm_2 _)
