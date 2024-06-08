import Coin.DSubgroup

open Set

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)
variable (H : AddSubgroup G) [hCFH : CloseF f H]
variable (K : AddSubgroup G) [hCFK : CloseF f K]

def D_Supergroup : AddSubgroup G where
  carrier := (D f) ⁻¹' K ∩ H
  add_mem' := by
    rintro _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact
    ⟨
      mem_preimage.mpr <| map_add (D f) _ _ ▸ K.add_mem' hx hy,
      H.add_mem' hx' hy'
    ⟩
  neg_mem' := by
    rintro _ ⟨h, h'⟩
    exact ⟨mem_preimage.mpr <| map_neg (D f) _ ▸ K.neg_mem' h, H.neg_mem' h'⟩
  zero_mem' :=
    ⟨mem_preimage.mpr <| (map_zero (D f)).symm ▸ K.zero_mem', H.zero_mem'⟩

instance : CloseF f (D_Supergroup f H K) where
  image_closed := by
    rintro _ ⟨hx, hx'⟩
    exact ⟨
      mem_preimage.mpr <|
      (D_f_comm f _) ▸ hCFK.image_closed hx, hCFH.image_closed hx'
    ⟩

theorem D_Supergroup_le : D_Supergroup f H K ≤ H := by
  rintro _ ⟨_, h⟩; exact h
