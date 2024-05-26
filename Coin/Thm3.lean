import Coin.DCore
import Coin.Thm2

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

theorem D_core_bot_of_unique_CloseD
    (h : ∀ (H : AddSubgroup G), CloseD f ⊤ H → H = ⊤) : D_core f = ⊥ := by
  contrapose! h
  rcases
    upward_ssub _ (D_rank _)
    ⟨
      ⊥, bot_lt_iff_ne_bot.mpr h, bot_CloseF _,
      bot_CloseD_of_eq _ _ (D_core_eq_D_Subgroup _).symm
    ⟩
    with ⟨H, hH, _, hHCD⟩
  exact ⟨H, hHCD, ne_of_lt hH⟩

theorem unique_CloseD_of_D_core_bot (h : D_core f = ⊥) (H : AddSubgroup G)
    (hCD : CloseD f ⊤ H) : H = ⊤ := by
  contrapose! h
  rcases
    @downward_ssub _ _ f _ (lt_top_iff_ne_top.mpr h)
    (CloseF_of_CloseD hCD) hCD (D_rank f)
    with ⟨K, hK, _, _⟩
  exact (ne_of_lt (lt_of_le_of_lt bot_le hK)).symm

theorem thm_3 (hWin : isAttackWin f) : D_core f = ⊥ :=
  D_core_bot_of_unique_CloseD _ (fun _ h ↦ thm_2 h hWin)
