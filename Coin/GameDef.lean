import Coin.Common

variable {G : Type*} [Fintype G][AddCommGroup G]
variable (f : G ≃+ G)

def play (x₀ : G) (𝒜 : ℕ → G) (𝒟 : ℕ → ℕ) : ℕ → G
  | 0 => x₀
  | n + 1 => (f ^ 𝒟 n) (play x₀ 𝒜 𝒟 n) + 𝒜 n

def isAttackWin : Prop :=
  ∃ 𝒜 : ℕ → G, ∀ (x₀ : G) (𝒟 : ℕ → ℕ),
  ∃ n < Fintype.card G, play f x₀ 𝒜 𝒟 n = 0
