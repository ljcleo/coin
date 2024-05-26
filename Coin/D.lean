import Coin.CloseF

open Set SetLike

variable {G : Type*} [Fintype G] [AddCommGroup G]

variable (f : G ≃+ G)

def D : G →+ G := AddMonoidHom.mk'
  (fun a ↦ f a - a)
  (fun _ _ ↦ by dsimp; rw [map_add]; abel)

theorem D_f_comm (x : G) : D f (f x) = f (D f x) := by dsimp [D]; rw [map_sub]

variable (H : AddSubgroup G) [hCF : CloseF f H]

theorem D_maps_to_self_of_CloseF : MapsTo (D f) H H := fun _ hx ↦ by
  dsimp [D]; refine sub_mem ?_ hx; exact hCF.image_closed hx

theorem D_bijOn_of_D_image_eq {f : G ≃+ G} {H : AddSubgroup G}
    (h : (D f) '' H = H) : BijOn (D f) H H :=
  (
    Finite.surjOn_iff_bijOn_of_mapsTo H.instFiniteSubtypeMem
    fun x hx ↦ h ▸ ⟨x, hx, rfl⟩
  ).mp fun _ h' ↦ by rcases h.symm ▸ h' with ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
