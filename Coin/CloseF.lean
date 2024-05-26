import Coin.Common

open AddSubgroup Set

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

class CloseF (H : AddSubgroup G) : Prop where
  image_closed : MapsTo f H H

instance bot_CloseF : CloseF f ⊥ where
  image_closed := fun x _ ↦ by
    rw [coe_bot, mem_singleton_iff] at *; subst x; exact f.map_zero

instance top_CloseF : CloseF f ⊤ where
  image_closed := fun _ _ ↦ mem_univ _
