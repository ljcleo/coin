import Coin.Common

open AddAut AddSubgroup Set

variable {G : Type*} [Fintype G] [AddCommGroup G]

class CloseF (f : G ≃+ G) (H : AddSubgroup G) : Prop where
  image_closed : MapsTo f H H

section

variable {f : G ≃+ G}

instance : CloseF f ⊥ where
  image_closed := fun x _ ↦ by
    rw [coe_bot, mem_singleton_iff] at *; subst x; exact f.map_zero

instance top_CloseF : CloseF f ⊤ where
  image_closed := fun _ _ ↦ mem_univ _

end

theorem f_pow_mem_of_mem (f : G ≃+ G) {H : AddSubgroup G} [h : CloseF f H]
    {x : G} (hx : x ∈ H) (i : ℕ) : (f ^ i) x ∈ H := by
  induction' i with i ih
  · exact hx
  exact (pow_succ' f _).symm ▸ (mul_apply _ f _ _).symm ▸ (h.image_closed ih)
