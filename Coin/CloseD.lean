import Coin.Common
import Coin.D

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

class CloseD {H : Set G} {K : Set G} (hk : K ⊆ H) where
  D_preimage_self : (D f) ⁻¹' K ∩ H = K

instance top_CloseD : CloseD f (le_refl ⊤) where
  D_preimage_self := by rw [Set.top_eq_univ, Set.preimage_univ, Set.inter_self]
