import Coin.Common
import Coin.Util
import Coin.CloseF
import Coin.D
import Coin.CloseD

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)
variable (H : AddSubgroup G) [hCF : CloseF f H]

def D_Subgroup : AddSubgroup G := (D_Lim f H).range.map H.subtype

instance D_Subgroup_CloseF : CloseF f (D_Subgroup f H) where
  image_closed := by
    dsimp [D_Subgroup, D_Lim, D]; rintro a ⟨b, ⟨c, hc⟩, hab⟩; subst a; subst b
    dsimp; set d : G := c.val; rw [Set.mem_image, Subtype.exists]
    have hd : d ∈ H := Subtype.mem _
    have hfd : f d ∈ H := hCF.image_closed hd
    use f (f d - d), hCF.image_closed (sub_mem hfd hd)
    dsimp; rw [eq_self, and_true, Set.mem_range, Subtype.exists]
    use f d, hfd; ext; rw [Set.MapsTo.val_restrict_apply, ← map_sub]

lemma D_Subgroup_cast {H₁ H₂ : AddSubgroup G} [CloseF f H₁] [CloseF f H₂]
    (h : H₁ = H₂): D_Subgroup f H₁ = D_Subgroup f H₂ := by subst H₁; rfl

lemma D_Subgroup_le : D_Subgroup f H ≤ H :=
  AddSubgroup.map_subtype_le (D_Lim f H).range

def D_Subgroup_Hom : H →+ D_Subgroup f H :=
  let hom := D_Lim f H; (Hom_range_back_Hom hom).comp hom.rangeRestrict

lemma D_Subgroup_Hom_bijective_of_eq (h : D_Subgroup f H = H) :
    Function.Bijective (D_Subgroup_Hom f H) :=
  let surj : Function.Surjective (D_Subgroup_Hom f H) := by
    rintro ⟨y, hy⟩; dsimp [D_Subgroup_Hom]; rw [Subtype.exists]
    rcases AddSubgroup.mem_map.mp hy with ⟨x, ⟨z, hz⟩, hxy⟩
    use z, (Subtype.mem _); subst x y
    trans
    · exact AddMonoidHom.comp_apply
        (Hom_range_back_Hom (D_Lim f H)) (D_Lim f H).rangeRestrict _
    unfold AddMonoidHom.rangeRestrict
    rw [Subtype.coe_eta, AddMonoidHom.codRestrict_apply];
    ext; dsimp [Hom_range_back_Hom]
  ⟨(Finite.injective_iff_surjective_of_equiv (by rw [h])).mpr surj, surj⟩

-- noncomputable def D_Subgroup_Equiv_of_eq (h : D_Subgroup f H = H) :
--     H ≃+ D_Subgroup f H := AddEquiv.mk'
--   (
--     Equiv.ofBijective (D_Subgroup_Hom f H)
--     (D_Subgroup_Hom_bijective_of_eq f H h)
--   )
--   fun x y ↦ by ext; rw [
--     Equiv.ofBijective_apply, Equiv.ofBijective_apply,
--     Equiv.ofBijective_apply, map_add
--   ]

-- noncomputable def D_Aut_of_D_Subgroup_eq (h : D_Subgroup f H = H) :
--   H ≃+ H := (D_Subgroup_Equiv_of_eq f H h).trans (by rw [h])

instance bot_CloseD_of_eq (h : D_Subgroup f H = H) : CloseD f (@bot_le _ _ _ H) where
  D_preimage_self := by
    rw [AddSubgroup.coe_bot]
    ext x
    rw [
      Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, SetLike.mem_coe
    ]
    constructor
    · rintro ⟨hDfx, hx⟩
      let z : H := Subtype.mk x hx
      have (x : H) (hx : D_Subgroup_Hom f H x = 0) : x = 0 := by
        rw [← (map_zero _ : D_Subgroup_Hom f H 0 = 0)] at hx
        exact (D_Subgroup_Hom_bijective_of_eq f H h).injective hx
      have : z = 0 := by
        apply this z; dsimp [D_Subgroup_Hom]
        trans
        · exact AddMonoidHom.comp_apply
            (Hom_range_back_Hom (D_Lim f H)) (D_Lim f H).rangeRestrict _
        unfold AddMonoidHom.rangeRestrict; rw [AddMonoidHom.codRestrict_apply]
        ext; dsimp [Hom_range_back_Hom, D_Lim]; exact hDfx
      dsimp [z] at this
      rwa [← AddSubmonoid.mk_eq_zero]
    intro hx; subst x; exact ⟨map_zero _, H.zero_mem⟩
