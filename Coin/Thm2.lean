import Coin.Common
import Coin.GameDef
import Coin.CloseD

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)
variable (H : AddSubgroup G) [hCD : CloseD f (@le_top _ _ _ H)]

lemma lem_2_1 {a : G} (b : G) (ha : a ∉ H) : ∃ z : ℕ, (f ^ z) a + b ∉ H := by
  by_cases h : a + b ∈ H
  · use 1; simp; contrapose! ha
    have : (D f) a ∈ H := calc
      _ = f a - a := by dsimp [D]
      _ = f a + b - (a + b) := by abel
      _ ∈ H := sub_mem ha h
    rwa [
      ← SetLike.mem_coe, ← hCD.D_preimage_self, AddSubgroup.coe_top,
      Set.inter_univ, Set.mem_preimage, SetLike.mem_coe
    ]
  use 0; rwa [pow_zero, AddAut.one_apply]

lemma lem_2_2 {x₀ : G} {𝒜 : ℕ → G} {𝒟 : ℕ → ℕ} {n : ℕ}
    (h𝒟 : ∀ k ≤ n, play f x₀ 𝒜 𝒟 k ∉ H) :
    ∃ 𝒟' : ℕ → ℕ, ∀ k ≤ n + 1, play f x₀ 𝒜 𝒟' k ∉ H := by
  rcases lem_2_1 f _ (𝒜 n) (h𝒟 _ (le_refl _)) with ⟨z, hz⟩
  let 𝒟' : ℕ → ℕ := Function.update 𝒟 n z
  have h (k : ℕ) (hk : k ≤ n) : play f x₀ 𝒜 𝒟 k = play f x₀ 𝒜 𝒟' k := by
    induction' k with k ih
    · dsimp [play]
    dsimp [play]; rw [ih (Nat.le_of_succ_le hk)]; congr
    dsimp [𝒟']; rw [Function.update_noteq (ne_of_lt (Nat.lt_of_succ_le hk))]
  use 𝒟'; intro k hk
  by_cases hkn : k = n + 1
  · rw [hkn]; dsimp [play]; rw [← h n (le_refl n)]
    dsimp [𝒟']; rwa [Function.update_same]
  have : k ≤ n := (Nat.le_of_lt_succ (lt_of_le_of_ne hk hkn))
  rw [← h k this]; exact h𝒟 k this

lemma lem_2_3 (x₀ : G) (hx₀ : x₀ ∉ H) (𝒜 : ℕ → G) (n : ℕ) :
    ∃ 𝒟 : ℕ → ℕ, ∀ k ≤ n, play f x₀ 𝒜 𝒟 k ∉ H := by
  induction' n with n ih
  · use fun _ ↦ 0; intro _ hk
    rw [Nat.eq_zero_of_le_zero hk]; dsimp [play]; exact hx₀
  rcases ih with ⟨_, h𝒟⟩; exact lem_2_2 f _ h𝒟

lemma lem_2_4 (hWin : isAttackWin f) (x₀ : G) : x₀ ∈ H := by
  contrapose! hWin; dsimp [isAttackWin]; push_neg
  intro 𝒜; rcases lem_2_3 f _ _ hWin 𝒜 (Fintype.card G) with ⟨𝒟, h𝒟⟩
  use x₀, 𝒟; intro n hn
  have := h𝒟 n (le_of_lt hn)
  contrapose! this; rw [this]; exact H.zero_mem

theorem thm_2 (hWin : isAttackWin f) : H = ⊤ :=
  H.eq_top_iff'.mpr (fun x ↦ lem_2_4 f _ hWin x)

def thm_2_iso (hWin : isAttackWin f) : G ≃+ H := by
  rw [thm_2 f H hWin]; exact AddSubgroup.topEquiv.symm
