import Coin.CloseD
import Coin.GameDef

open AddSubgroup List

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable {f : G ≃+ G}
variable {H : AddSubgroup G} (hCD : CloseD f ⊤ H)

theorem exist_𝒟 {x₀ : G} (hx : x₀ ∉ H) (𝒜 : List G) :
    ∃ 𝒟 : List ℕ, ∀ i ≤ n, play f x₀ 𝒜 𝒟 i ∉ H := by
  induction' n with n ih generalizing x₀ 𝒜
  · use nil; intro i h; rw [Nat.eq_zero_of_le_zero h, play]; exact hx
  rcases 𝒜 with _ | ⟨a, 𝒜⟩
  · use nil; intro i h; rcases i with _ | i <;> (rw [play]; exact hx)
  rcases avoid_of_CloseD hCD (mem_top _) hx a with ⟨d, hd⟩
  rcases ih hd 𝒜 with ⟨𝒟, h𝒟⟩
  use d :: 𝒟; intro i h
  rcases i with _ | i
  · rw [play]; exact hx
  rw [play]; exact h𝒟 _ <| Nat.le_of_succ_le_succ h

variable (hWin : isAttackWin f)

theorem start_in_H_of_attackWin (x₀ : G) : x₀ ∈ H := by
  rcases hWin with ⟨𝒜, h⟩; contrapose! h
  rcases exist_𝒟 hCD h 𝒜 with ⟨𝒟, h𝒟⟩
  use x₀, 𝒟; intro n h; have h' := h𝒟 n h; contrapose! h'
  exact h' ▸ H.zero_mem

theorem thm_2 : H = ⊤ :=
  H.eq_top_iff'.mpr fun _ ↦ start_in_H_of_attackWin hCD hWin _
