import Coin.Common

variable {G : Type*} [Fintype G] [AddCommGroup G]

def Hom_range_back_Hom {H : AddSubgroup G} (hom : H →+ H) :
    hom.range →+ hom.range.map H.subtype  :=
  AddMonoidHom.mk'
  (
    Set.MapsTo.restrict H.subtype hom.range (hom.range.map H.subtype)
    fun x _ ↦ by use x
  )
  fun _ _ ↦ by ext; rw [
    AddSubmonoid.coe_add, Set.MapsTo.val_restrict_apply,
    Set.MapsTo.val_restrict_apply, Set.MapsTo.val_restrict_apply,
    AddSubmonoid.coe_add, AddSubgroup.coeSubtype, AddSubmonoid.coe_add
  ]
