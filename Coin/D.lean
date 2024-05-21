import Coin.Common
import Coin.CloseF

variable {G : Type*} [Fintype G] [AddCommGroup G]

def Hom_range_back_Hom {H : AddSubgroup G} (hom : H →+ H) :
    hom.range →+ hom.range.map H.subtype  :=
  AddMonoidHom.mk'
  (
    Set.MapsTo.restrict H.subtype hom.range (hom.range.map H.subtype)
    fun x hx ↦ by
      simp; rcases AddMonoidHom.mem_range.mp hx with ⟨y, hxy⟩; use y; simpa
  )
  fun _ _ ↦ by ext; simp

variable (f : G ≃+ G)

def D : G →+ G := AddMonoidHom.mk'
  (fun a ↦ f a - a)
  (fun _ _ ↦ by dsimp; rw [map_add]; abel)

variable (H : AddSubgroup G) [hCF : CloseF f H]

lemma D_maps_to_self_of_CloseF : Set.MapsTo (D f) H H := fun _ hx ↦ by
  dsimp [D]; refine sub_mem ?_ hx
  rw [← SetLike.mem_coe]; exact hCF.image_closed hx

def D_Lim : H →+ H := AddMonoidHom.mk'
  (Set.MapsTo.restrict (D f) H H (D_maps_to_self_of_CloseF _ _))
  fun _ _ ↦ by ext; dsimp; rw [map_add]

def D_Subgroup : AddSubgroup G := (D_Lim f H).range.map H.subtype

def D_Subgroup_Hom : H →+ D_Subgroup f H :=
  let hom := D_Lim f H; (Hom_range_back_Hom hom).comp hom.rangeRestrict

theorem D_Subgroup_le : D_Subgroup f H ≤ H := AddSubgroup.map_subtype_le (D_Lim f H).range

instance D_Subgroup_CloseF : CloseF f (D_Subgroup f H) where
  image_closed := by
    simp [D_Subgroup, D_Lim]; intro x hx
    have hfx : f x ∈ H := hCF.image_closed hx
    have : f ((D f) x) ∈ H := by simp [D]; exact sub_mem (hCF.image_closed hfx) hfx
    use this, f x, hfx; ext; simp [D]

theorem D_Subgroup_cast {H₁ H₂ : AddSubgroup G} [CloseF f H₁] [CloseF f H₂] (h : H₁ = H₂):
    D_Subgroup f H₁ = D_Subgroup f H₂ := by
  simp [D_Subgroup, D_Lim]
  ext x
  constructor <;>
  · rintro ⟨a, ha, hax⟩
    simp
    aesop_subst [hax, h]
    simp_all only [AddMonoidHom.coe_range,
      AddMonoidHom.mk'_apply,
      Set.mem_range,
      Subtype.exists,
      AddSubgroup.coeSubtype,
      Subtype.coe_eta,
      SetLike.coe_mem,
      exists_const]
