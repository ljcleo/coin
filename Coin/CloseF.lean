import Coin.Common

open AddAut AddSubgroup Set

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

class CloseF (H : AddSubgroup G) : Prop where
  image_closed : MapsTo f H H

instance bot_CloseF : CloseF f ⊥ where
  image_closed := fun x _ ↦ by
    rw [coe_bot, mem_singleton_iff] at *; subst x; exact f.map_zero

instance top_CloseF : CloseF f ⊤ where
  image_closed := fun _ _ ↦ mem_univ _

variable (H : AddSubgroup G) [h : CloseF f H]

theorem f_bijOn_of_CloseF : BijOn f H H :=
  (
    Finite.injOn_iff_bijOn_of_mapsTo H.instFiniteSubtypeMem
    fun _ hx ↦ h.image_closed hx
  ).mp fun _ _ _ _ hxy ↦ f.injective hxy

theorem f_pow_mem_of_mem {x : G} (hx : x ∈ H) (i : ℕ) : (f ^ i) x ∈ H := by
  induction' i with i ih
  · exact hx
  exact (pow_succ' f _).symm ▸ (mul_apply _ f _ _).symm ▸ (h.image_closed ih)
