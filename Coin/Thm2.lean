import Coin.CloseD
import Coin.GameDef

open AddSubgroup Fintype Function

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable {f : G ≃+ G}
variable {H : AddSubgroup G} (hCD : CloseD f ⊤ H)

theorem construct_𝒟 {x₀ : G} {𝒜 : ℕ → G} {𝒟 : ℕ → ℕ} {n : ℕ}
    (h𝒟 : ∀ k ≤ n, play f x₀ 𝒜 𝒟 k ∉ H) :
    ∃ 𝒟' : ℕ → ℕ, ∀ k ≤ n + 1, play f x₀ 𝒜 𝒟' k ∉ H := by
  rcases
    can_keep_out_of_CloseD hCD (𝒜 n)
    (mem_top _) (h𝒟 _ (le_refl _)) with ⟨z, hz⟩
  let 𝒟' : ℕ → ℕ := update 𝒟 n z
  have h (k : ℕ) (hk : k ≤ n) : play f x₀ 𝒜 𝒟 k = play f x₀ 𝒜 𝒟' k := by
    induction' k with k ih
    · rfl
    dsimp [play]; rw [ih (Nat.le_of_succ_le hk)]; congr
    dsimp [𝒟']; rw [update_noteq (ne_of_lt (Nat.lt_of_succ_le hk))]
  use 𝒟'; intro k hk
  by_cases hkn : k = n + 1
  · subst k; dsimp [play]; rw [← h n (le_refl n)]
    dsimp [𝒟']; rwa [update_same]
  have : k ≤ n := (Nat.le_of_lt_succ (lt_of_le_of_ne hk hkn))
  rw [← h k this]; exact h𝒟 k this

theorem exist_𝒟 {x₀ : G} (hx₀ : x₀ ∉ H) (𝒜 : ℕ → G) (n : ℕ) :
    ∃ 𝒟 : ℕ → ℕ, ∀ k ≤ n, play f x₀ 𝒜 𝒟 k ∉ H := by
  induction' n with n ih
  · use fun _ ↦ 0; intro _ hk; rw [Nat.eq_zero_of_le_zero hk]; exact hx₀
  rcases ih with ⟨_, h𝒟⟩; exact construct_𝒟 hCD h𝒟

theorem start_in_H_of_attackWin (hWin : isAttackWin f) (x₀ : G) : x₀ ∈ H := by
  rcases hWin with ⟨𝒜, h⟩; contrapose! h
  rcases exist_𝒟 hCD h 𝒜 (card G) with ⟨𝒟, h𝒟⟩
  exact ⟨_, _, fun _ hn h' ↦ h' ▸ h𝒟 _ (le_of_lt hn) <| H.zero_mem⟩

theorem thm_2 (hWin : isAttackWin f) : H = ⊤ :=
  H.eq_top_iff'.mpr fun _ ↦ start_in_H_of_attackWin hCD hWin _
