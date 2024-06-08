import Coin.DChain

open AddSubgroup Equiv Finite Function QuotientAddGroup Set

variable {G : Type*} [Fintype G] [AddCommGroup G]

section

variable (f : G ≃+ G)
variable (i : ℕ)

def chain_quot_hom : G →+ G ⧸ D_chain f (i + 1) :=
  QuotientAddGroup.mk' (D_chain f (i + 1))

def chain_quot : Set (G ⧸ D_chain f (i + 1)) :=
  chain_quot_hom f i '' (D_chain f i : Set G)

theorem chain_quot_card_eq_relindex :
    Nat.card (chain_quot f i) = (D_chain f (i + 1)).relindex (D_chain f i) :=
  (
    ker_mk' (D_chain f (i + 1)) ▸
    relindex_ker (chain_quot_hom f i) (D_chain f i)
  ).symm

end

section

variable {f : G ≃+ G}
variable {i : ℕ}

theorem exist_chain_quot_inv (a : chain_quot f i) :
    ∃ x : D_chain f i, chain_quot_hom f i x.val = a.val := by
  rcases a.prop with ⟨x, hx, h⟩; exact ⟨⟨x, hx⟩, h⟩

instance : Add (chain_quot f i) where
  add := fun a b ↦
    ⟨
      a.val + b.val,
      by
        rcases exist_chain_quot_inv a with ⟨x, hx⟩
        rcases exist_chain_quot_inv b with ⟨y, hy⟩
        exact ⟨x + y, add_mem x.prop y.prop, hx ▸ hy ▸ map_add _ _ _⟩
    ⟩

instance : Neg (chain_quot f i) where
  neg := fun a ↦
    ⟨
      -a.val,
      by
        rcases exist_chain_quot_inv a with ⟨x, hx⟩
        exact ⟨-x, neg_mem x.prop, hx ▸ map_neg _ _⟩
    ⟩

instance : Zero (chain_quot f i) where
  zero := ⟨0, _, zero_mem _, map_zero _⟩

instance : AddGroup (chain_quot f i) :=
  AddGroup.ofLeftAxioms (fun _ _ _ ↦ by ext; exact add_assoc _ _ _)
  (fun _ ↦ by ext; exact zero_add _) (fun _ ↦ by ext; exact add_left_neg _)

def chain_quot_chain_hom : D_chain f i →+ chain_quot f i := AddMonoidHom.mk'
  (fun x ↦ ⟨chain_quot_hom f i x.val, x.val, x.prop, rfl⟩)
  (fun x y ↦ by ext; dsimp; rw [map_add]; rfl)

def lift_chain (x : D_chain f (i + 1)) : D_chain f i :=
  ⟨x.val, mem_of_subset_of_mem (D_chain_adj_le f _) x.prop⟩

theorem hom_lift_chain_eq_zero (x : D_chain f (i + 1)) :
    chain_quot_chain_hom (lift_chain x) = 0 := by
  rw [
    lift_chain, chain_quot_chain_hom, AddMonoidHom.mk'_apply, Subtype.mk.injEq,
    chain_quot_hom, mk'_apply
  ]
  convert (eq_zero_iff _).mpr x.prop

theorem chain_quot_chain_hom_surj :
    Surjective (@chain_quot_chain_hom _ _ f i) := fun a ↦ by
  rcases exist_chain_quot_inv a with ⟨x, hx⟩; use x; ext; exact hx

noncomputable def chain_quot_rep :
    chain_quot f i → D_chain f i := surjInv chain_quot_chain_hom_surj

instance : Nonempty (chain_quot f i) := Zero.instNonempty

instance : Zero (Fin (Nat.card (chain_quot f i))) where
  zero := ⟨0, Nat.card_pos⟩

noncomputable def chain_quot_equivFin :
    chain_quot f i ≃ Fin (Nat.card (chain_quot f i)) :=
  let g := equivFin (chain_quot _ _); g.trans <| swap 0 <| g 0

theorem chain_quot_equivFin_zero_eq_zero :
    (@chain_quot_equivFin _ _ _ f i) 0 = 0 := by
  dsimp [chain_quot_equivFin]; rw [swap_apply_right]

theorem chain_quot_equivFin_symm_zero_eq_zero :
    (@chain_quot_equivFin _ _ _ f i).symm 0 = 0 :=
  (
    symm_apply_apply _ _ ▸
    congrArg chain_quot_equivFin.symm chain_quot_equivFin_zero_eq_zero
  ).symm

end
