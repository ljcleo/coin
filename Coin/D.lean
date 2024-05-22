import Coin.Common
import Coin.CloseF

variable {G : Type*} [Fintype G] [AddCommGroup G]

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
