import Coin.Common

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

class CloseF (H : Set G) where
  image_closed : H.MapsTo f H

instance top_CloseF : CloseF f ⊤ where
  image_closed := fun x _ ↦ by trivial

variable (H : AddSubgroup G) [h : CloseF f H]

lemma f_bijOn_self_of_CloseF : Set.BijOn f H H := by
    rw [← Set.Finite.injOn_iff_bijOn_of_mapsTo
           (AddSubgroup.instFiniteSubtypeMem _)
           h.image_closed]
    exact fun _ _ _ _ hxy ↦ f.injective hxy

noncomputable def f_Lim : H ≃+ H := AddEquiv.mk'
  (
    Equiv.ofBijective
    (Set.MapsTo.restrict f H H h.image_closed)
    (f_bijOn_self_of_CloseF _ _).bijective
  )
  (fun _ _ ↦ by ext; dsimp; rw [map_add])
