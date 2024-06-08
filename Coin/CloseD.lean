import Coin.D

open Set SetLike

variable {G : Type*} [Fintype G] [AddCommGroup G]

def CloseD (f : G ≃+ G) (H K : AddSubgroup G) : Prop := (D f) ⁻¹' K ∩ H = K

variable {f : G ≃+ G}
variable {H : AddSubgroup G} [hCFH : CloseF f H]
variable {K : AddSubgroup G}
variable (hCD : CloseD f H K)
variable {a : G} (ha : a ∈ H)

theorem Subgroup_of_CloseD : K ≤ H :=
  fun _ h ↦ (subset_of_subset_of_eq (Subset.refl _) hCD.symm h).right

instance CloseF_of_CloseD : CloseF f K where
  image_closed := fun x h ↦
    (sub_add_cancel (f x) _).symm ▸
    add_mem ((subset_of_subset_of_eq (Subset.refl _) hCD.symm h).left) h

theorem preimage_close_of_CloseD (hDfa : (D f) a ∈ K) : a ∈ K := by
  rw [← mem_coe, ← hCD]; exact ⟨hDfa, ha⟩

theorem avoid_of_CloseD (haK : a ∉ K) (b : G) : ∃ z : ℕ, (f ^ z) a + b ∉ K := by
  by_cases h : a + b ∈ K
  · use 1; rw [pow_one]; contrapose! haK
    apply preimage_close_of_CloseD hCD ha; dsimp [D]
    rw [← add_sub_add_right_eq_sub _ _ b]; exact sub_mem haK h
  use 0; convert h
