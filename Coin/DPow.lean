import Coin.DCore

open Function Set

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem D_pow_mem_D_chain' {f : G ≃+ G} {n : ℕ} {x : G} (h : x ∈ D_chain f n)
    (m : ℕ) : (D f)^[m] x ∈ D_chain f (n + m) := by
  induction' m with m ih
  · exact h
  rw [iterate_succ_apply']; use (D f)^[m] x, ih

section

variable (f : G ≃+ G)
variable (x : G)

theorem D_pow_mem_D_chain (n : ℕ) : (D f)^[n] x ∈ D_chain f n := by
  have : x ∈ D_chain f 0 := mem_univ _
  convert D_pow_mem_D_chain' this _; rw [Nat.zero_add]

theorem D_pow_rank_mem_core : (D f)^[D_rank f] x ∈ D_core f :=
  D_pow_mem_D_chain f x (D_rank f)

end

variable {f : G ≃+ G}
variable {x : G}

theorem D_add_pow_zero_of_pow_zero
    {p q : ℕ} (h : (D f)^[p] x = 0) : (D f)^[q + p] x = 0 := by
  rw [iterate_add_apply, h]; exact iterate_map_zero _ _

theorem D_pow_zero_of_le_pow_zero
    {p q : ℕ} (h : p ≤ q) (h' : (D f)^[p] x = 0) : (D f)^[q] x = 0 := by
  rw [← Nat.add_sub_cancel' h, Nat.add_comm]
  exact D_add_pow_zero_of_pow_zero h'

theorem D_pow_ne_zero_of_loop
    (h : ∃ p q : ℕ, 0 < q ∧ (D f)^[p] x ≠ 0 ∧ (D f)^[q + p] x = (D f)^[p] x)
    (n : ℕ) : (D f)^[n] x ≠ 0 := by
  rcases h with ⟨p, q, h₁, h₂, h₃⟩
  have (k : ℕ) : (D f)^[k * q + p] x = (D f)^[p] x := by
    induction' k with k ih
    · rw [Nat.zero_mul, Nat.zero_add]
    rw [
      Nat.succ_mul, Nat.add_comm _ q, Nat.add_assoc, iterate_add_apply, ih,
      ← iterate_add_apply
    ]
    exact h₃
  contrapose! h₂
  rw [← this n]
  exact
    D_pow_zero_of_le_pow_zero
    ((Nat.le_mul_of_pos_right _ h₁).trans <| Nat.le_add_right _ _) h₂

theorem D_pow_ne_zero_of_mem_core_of_ne_zero
    (h : x ∈ D_core f) (h' : x ≠ 0) (n : ℕ) : (D f)^[n] x ≠ 0 := by
  have h'' (m : ℕ) : (D f)^[m] x ∈ D_core f := by
    induction' m with m ih
    · exact h
    rw [iterate_succ_apply', D_core, (D_rank_is_bound _).succ]
    use (D f)^[m] x, ih
  induction' n with n ih
  · exact h'
  rw [iterate_succ_apply']; exact D_ne_zero_of_mem_core_of_ne_zero (h'' n) ih
