import Coin.D

open AddAut AddSubgroup Set SetLike

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable (f : G ≃+ G)

def CloseD (H K : AddSubgroup G) : Prop := (D f) ⁻¹' K ∩ H = K

theorem self_CloseD (H : AddSubgroup G) [hCF : CloseF f H] : CloseD f H H :=
    inter_eq_right.mpr fun _ h ↦ sub_mem (hCF.image_closed h) h

variable {f : G ≃+ G}
variable {H : AddSubgroup G} [hCFH : CloseF f H]
variable {K : AddSubgroup G}
variable (hCD : CloseD f H K)

theorem Subgroup_of_CloseD : K ≤ H :=
  fun _ h ↦ (subset_of_subset_of_eq (Subset.refl _) hCD.symm h).right

instance CloseF_of_CloseD : CloseF f K where
  image_closed := fun x h ↦ calc
    _ = D f x + x := by dsimp [D]; abel
    _ ∈ K :=
      add_mem ((subset_of_subset_of_eq (Subset.refl _) hCD.symm h).left) h

theorem preimage_close_of_CloseD {a : G} (ha : a ∈ H) (hDfa : (D f) a ∈ K) :
    a ∈ K := by rw [← mem_coe, ← hCD]; exact ⟨hDfa, ha⟩

theorem can_keep_out_of_CloseD {a : G} (b : G) (ha : a ∈ H) (haK : a ∉ K) :
    ∃ z : ℕ, (f ^ z) a + b ∉ K := by
  by_cases h : a + b ∈ K
  · use 1; rw [pow_one]; contrapose! haK
    apply preimage_close_of_CloseD hCD ha; dsimp [D]
    rw [← add_sub_add_right_eq_sub _ _ b]; exact sub_mem haK h
  use 0; convert h
