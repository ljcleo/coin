import Coin.DPow

open AddSubgroup

variable {G : Type*} [Fintype G] [AddCommGroup G]

section

variable {f : G ≃+ G}

theorem core_eq_bot_of_all_contract (h : ∀ x : G, ∃ n : ℕ, (D f)^[n] x = 0) :
    D_core f = ⊥ := by
  rw [eq_bot_iff_forall]; intro x hx; by_contra! h'; rcases h x with ⟨k, hk⟩
  exact D_pow_ne_zero_of_mem_core_of_ne_zero hx h' k hk

theorem all_contract_of_core_eq_bot (h : D_core f = ⊥) (x : G) :
    ∃ n : ℕ, (D f)^[n] x = 0 :=
  ⟨D_rank f, mem_bot.mp <| h ▸ D_pow_rank_mem_core f x⟩

end

theorem thm_5 (f : G ≃+ G) :
    D_core f = ⊥ ↔ ∀ x : G, ∃ n : ℕ, (D f)^[n] x = 0 :=
  ⟨all_contract_of_core_eq_bot, core_eq_bot_of_all_contract⟩
