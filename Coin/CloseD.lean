import Coin.Common
import Coin.D

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

class CloseD {H : Set G} {K : Set G} (hk : K ⊆ H) where
  D_preimage_self : (D f) ⁻¹' K ∩ H = K

instance : CloseD f (le_refl ⊤) where
  D_preimage_self := by simp
