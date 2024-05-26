import Coin.CloseD

open AddMonoidHom AddSubgroup Finite Function Set SetLike

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)
variable (H : AddSubgroup G) [hCF : CloseF f H]

def D_Subgroup : AddSubgroup G where
  carrier := (D f) '' H
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, H.add_mem hx hy, map_add _ _ _⟩
  neg_mem':= by
    rintro _ ⟨x, hx, rfl⟩; exact ⟨-x, H.neg_mem hx, map_neg _ _⟩
  zero_mem' := ⟨0, H.zero_mem, map_zero _⟩

instance D_Subgroup_CloseF : CloseF f (D_Subgroup f H) where
  image_closed := by
    rintro _ ⟨x, hx, rfl⟩; exact ⟨f x, hCF.image_closed hx, D_f_comm _ _⟩

theorem D_Subgroup_le : D_Subgroup f H ≤ H := by
  rintro _ ⟨x, hx, rfl⟩; exact D_maps_to_self_of_CloseF _ _ hx

theorem D_Subgroup_le_of_le {H K : AddSubgroup G} (hKH : K ≤ H) :
    D_Subgroup f K ≤ D_Subgroup f H := by
  rintro _ ⟨x, hx, rfl⟩; exact ⟨x, mem_of_subset_of_mem hKH hx, rfl⟩

theorem bot_CloseD_of_eq (h : D_Subgroup f H = H) : CloseD f H ⊥ :=
  ext fun _ ↦
    ⟨
      fun ⟨hDfx, hx⟩ ↦
        (D_bijOn_of_D_image_eq (congrArg (fun x ↦ x.carrier) h)).injOn
        hx H.zero_mem (hDfx.trans (map_zero (D f)).symm),
      fun h ↦ h ▸ ⟨map_zero _, H.zero_mem⟩
    ⟩
