import Coin.CloseD

open AddAction AddAut AddMonoidHom AddSubgroup Finite Function Set SetLike

variable {G : Type*} [Fintype G] [AddCommGroup G]

section

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

end

section

variable {f : G ≃+ G}
variable {H : AddSubgroup G} [hCF : CloseF f H]

theorem bot_CloseD_of_eq (h : D_Subgroup f H = H) : CloseD f H ⊥ :=
  ext fun _ ↦
    ⟨
      fun ⟨hDfx, hx⟩ ↦
        (D_bijOn_of_D_image_eq (congrArg (fun x ↦ x.carrier) h)).injOn
        hx H.zero_mem (hDfx.trans (map_zero (D f)).symm),
      fun h ↦ h ▸ ⟨map_zero _, H.zero_mem⟩
    ⟩

theorem f_pow_sub_mem_D_Subgroup {x : G} (h : x ∈ H) (i : ℕ) :
    (f ^ i) x - x ∈ D_Subgroup f H := by
  induction' i with i ih
  · rw [pow_zero, one_apply, sub_self]; exact zero_mem _
  calc
  _ = (f ^ (i + 1)) x - (f ^ i) x + ((f ^ i) x - x) := by
    rw [add_sub, sub_add_cancel]
  _ ∈ D_Subgroup f H :=
    add_mem
    (
      (pow_succ' f _).symm ▸ (mul_apply _ f _ _).symm ▸
      ⟨(f ^ i) x, f_pow_mem_of_mem _ _ h _, rfl⟩
    ) ih

theorem quot_map_f_pow_eq_quot_map {x : G} (h : x ∈ H) (i : ℕ) :
    QuotientAddGroup.mk' (D_Subgroup f H) ((f ^ i) x) =
    QuotientAddGroup.mk' (D_Subgroup f H) x :=
  (
    QuotientAddGroup.eq.mpr <|
    sub_eq_neg_add _ x ▸ f_pow_sub_mem_D_Subgroup h i
  ).symm

end
