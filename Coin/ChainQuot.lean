import Coin.DChain

open AddSubgroup Equiv Finite Function QuotientAddGroup Set

variable {G : Type*} [Fintype G] [AddCommGroup G]

section

variable (f : G ≃+ G)
variable (i : ℕ)

def chain_quot_hom : G →+ G ⧸ D_chain f (i + 1) :=
  QuotientAddGroup.mk' (D_chain f (i + 1))

def chain_quot (f : G ≃+ G) (i : ℕ) : AddSubgroup (G ⧸ D_chain f (i + 1)) :=
  (D_chain f i).map (chain_quot_hom f i)

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

def chain_quot_chain_hom : D_chain f i →+ chain_quot f i :=
  ((chain_quot_hom f i).restrict <| D_chain f i).codRestrict _
    fun x => AddSubgroup.mem_map.mpr ⟨x, x.prop, rfl⟩

def lift_chain (x : D_chain f (i + 1)) : D_chain f i :=
  ⟨x.val, mem_of_subset_of_mem (D_chain_adj_le f _) x.prop⟩

theorem hom_lift_chain_eq_zero (x : D_chain f (i + 1)) :
    chain_quot_chain_hom (lift_chain x) = 0 := Subtype.ext <| (eq_zero_iff _).mpr x.prop

theorem chain_quot_chain_hom_surj :
    Surjective (@chain_quot_chain_hom _ _ f i) := fun ⟨_, h⟩ => by
  obtain ⟨x, hx, h'⟩ := AddSubgroup.mem_map.mp h
  exact ⟨⟨x, hx⟩, Subtype.ext h'⟩

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
