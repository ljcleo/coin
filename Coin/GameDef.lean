import Coin.Common

open Fintype

variable {G : Type*} [Fintype G][AddCommGroup G]
variable (f : G ≃+ G)

def play (x₀ : G) : List G → List ℕ → ℕ → G
  | _, _, 0 => x₀
  | [], [], _ + 1 => x₀
  | a :: 𝒜, [], i + 1 => play (x₀ + a) 𝒜 [] i
  | [], d :: 𝒟, i + 1 => play ((f ^ d) x₀) [] 𝒟 i
  | a :: 𝒜, d :: 𝒟, i + 1 => play ((f ^ d) x₀ + a) 𝒜 𝒟 i

def isAttackWin : Prop :=
  ∃ 𝒜 : List G, ∀ (x₀ : G) (𝒟 : List ℕ), ∃ n : ℕ,
  n ≤ card G - 1 ∧ play f x₀ 𝒜 𝒟 n = 0
