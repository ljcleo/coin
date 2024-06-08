import Coin.DSupergroup

open Set

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable {f : G ≃+ G}
variable {H : AddSubgroup G} [hCFH : CloseF f H]
variable {K : AddSubgroup G}

section

variable (hCD : CloseD f H K)

theorem succ_CloseD :
    CloseD f (D_Subgroup f H) (D_Subgroup f K) := ext fun _ ↦ by
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, ⟨x, hx, rfl⟩⟩
    exact
    ⟨
      x,
      preimage_close_of_CloseD hCD hx <|
      preimage_close_of_CloseD hCD (D_maps_to_self_of_CloseF f H hx) <|
      hxy ▸ (@D_maps_to_self_of_CloseF _ _ f K <| CloseF_of_CloseD hCD) hy,
      rfl
    ⟩
  rintro ⟨x, hx, rfl⟩
  exact
  ⟨
    ⟨
      D f x, (@D_maps_to_self_of_CloseF _ _ f K <| CloseF_of_CloseD hCD) hx,
      rfl
    ⟩,
    ⟨x, mem_of_subset_of_mem (Subgroup_of_CloseD hCD) hx, rfl⟩
  ⟩

theorem D_Subgroup_lt_of_lt_of_CloseD (hKH : K < H) :
    D_Subgroup f K < D_Subgroup f H := by
  apply lt_of_le_of_ne (D_Subgroup_le_of_le _ <| le_of_lt hKH)
  rcases exists_of_ssubset hKH with ⟨x, hx, hk⟩
  contrapose! hk
  exact
    preimage_close_of_CloseD hCD hx <|
    mem_of_subset_of_mem (@D_Subgroup_le _ _ _ _ <| CloseF_of_CloseD hCD) <|
    hk ▸ ⟨x, hx, rfl⟩

end

theorem pred_CloseD (hCD : CloseD f (D_Subgroup f H) K) :
    CloseD f H (D_Supergroup f H K) := ext fun x ↦ by
  constructor
  · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨preimage_close_of_CloseD hCD ⟨x, h', rfl⟩ h, h'⟩
  rintro ⟨h, h'⟩
  exact
  ⟨
    ⟨
      (@D_maps_to_self_of_CloseF _ _ _ _ (CloseF_of_CloseD hCD)) h,
      D_maps_to_self_of_CloseF _ _ h'
    ⟩,
    h'
  ⟩

theorem D_Supergroup_lt_of_lt_of_CloseD (hKH : K < D_Subgroup f H) :
    D_Supergroup f H K < H := by
  apply lt_of_le_of_ne (D_Supergroup_le _ _ _)
  rcases exists_of_ssubset hKH with ⟨_, ⟨x, hx, rfl⟩, hk⟩
  contrapose! hk; rcases hk.symm ▸ hx with ⟨hx', _⟩; exact hx'
