import Coin.ElimList
import Coin.Thm3

open AddSubgroup Equiv Function List QuotientAddGroup Set Subtype

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable {f : G ≃+ G}

section

variable {i : ℕ}

def chain_full_play (x₀ : D_chain f i) :
    List (D_chain f i) → List ℕ → D_chain f i
  | [], _ => x₀
  | a :: 𝒜, [] => chain_full_play (x₀ + a) 𝒜 []
  | a :: 𝒜, d :: 𝒟 =>
    chain_full_play (⟨(f ^ d) x₀, f_pow_mem_of_mem _ x₀.prop _⟩ + a) 𝒜 𝒟

def chain_play (x₀ : D_chain f i) :
    List (D_chain f i) → List ℕ → ℕ → D_chain f i
  | _, _, 0 => x₀
  | [], [], _ + 1 => x₀
  | a :: 𝒜, [], i + 1 => chain_play (x₀ + a) 𝒜 [] i
  | [], d :: 𝒟, i + 1 =>
      chain_play ⟨(f ^ d) x₀, f_pow_mem_of_mem _ x₀.prop _⟩ [] 𝒟 i
  | a :: 𝒜, d :: 𝒟, i + 1 =>
      chain_play (⟨(f ^ d) x₀, f_pow_mem_of_mem _ x₀.prop _⟩ + a) 𝒜 𝒟 i

theorem chain_play_eq_play (x₀ : D_chain f i) (𝒜 : List (D_chain f i))
    (𝒟 : List ℕ) (z : ℕ) :
    chain_play x₀ 𝒜 𝒟 z = play f x₀.val (𝒜.map val) 𝒟 z := by
  induction' 𝒜 with a 𝒜 ih generalizing 𝒟 z x₀
  · induction' 𝒟 with _ _ ih' generalizing z x₀
    · rcases z with _ | _ <;> rfl
    rcases z with _ | i
    · rfl
    rw [map_nil, chain_play, play, ih', map_nil]
  rcases z with _ | _
  · rcases 𝒟 with _ | _ <;> rfl
  rcases 𝒟 with _ | _ <;> (rw [map_cons, chain_play, play, ih]; congr)

theorem chain_play_lift' (hi : i + 1 ≤ D_rank f) (x₀ : D_chain f (D_rank f - i))
    (𝒜 : List (D_chain f (D_rank f - i))) (𝒟 : List ℕ) (z : ℕ) :
    (chain_play x₀ 𝒜 𝒟 z).val =
    (chain_play (lift_chain' hi x₀) (𝒜.map (lift_chain' hi)) 𝒟 z).val := by
  rw [chain_play_eq_play, chain_play_eq_play, List.map_map]; congr

theorem chain_play_concat₁ (x₀ : D_chain f i) (𝒜 𝒜' : List (D_chain f i))
    (𝒟 : List ℕ) {z : ℕ} (hi : z ≤ 𝒜.length) :
    chain_play x₀ (𝒜 ++ 𝒜') 𝒟 z = chain_play x₀ 𝒜 𝒟 z := by
  induction' 𝒜 with _ _ ih generalizing 𝒟 z x₀
  · rcases z with _ | _
    · rw [chain_play, chain_play]
    contradiction
  rcases z with _ | _
  · rw [chain_play, chain_play]
  rcases 𝒟 with _ | _ <;>
  rw [cons_append, chain_play, chain_play, ih _ _ <| Nat.le_of_succ_le_succ hi]

theorem chain_play_concat₂ (x₀ : D_chain f i) (𝒜 𝒜' : List (D_chain f i))
    (𝒟 : List ℕ) (z : ℕ) : chain_play x₀ (𝒜 ++ 𝒜') 𝒟 (𝒜.length + z) =
    chain_play (chain_full_play x₀ 𝒜 𝒟) 𝒜' (𝒟.drop 𝒜.length) z := by
  induction' 𝒜 with _ _ ih generalizing 𝒟 x₀
  · rw [chain_full_play, nil_append, length_nil, drop_zero, zero_add]
  rw [cons_append, length_cons, Nat.succ_add]
  rcases 𝒟 with _ | _ <;> rw [chain_play, ih, chain_full_play]
  · rw [drop_nil, drop_nil]
  rw [drop_succ_cons]

def coset_full_play (x₀ : D_chain f i) (𝒜 : List (D_chain f i)) :
    chain_quot f i := ((x₀ :: 𝒜).map chain_quot_chain_hom).sum

theorem coset_full_play_eq_hom_chain_full_play (x₀ : D_chain f i)
    (𝒜 : List (D_chain f i)) (𝒟 : List ℕ) : coset_full_play x₀ 𝒜 =
    chain_quot_chain_hom (chain_full_play x₀ 𝒜 𝒟) := by
  rw [coset_full_play, map_cons, sum_cons]
  induction' 𝒜 with _ _ ih generalizing 𝒟 x₀
  · rw [map_nil, sum_nil, add_zero]; rfl
  rw [map_cons, sum_cons, ← add_assoc, ← map_add]
  rcases 𝒟 with _ | _
  · rw [chain_full_play, ← ih]
  rw [chain_full_play, ← ih]; apply congrArg (· + _)
  rw [
    chain_quot_chain_hom, AddMonoidHom.mk'_apply, Subtype.mk.injEq,
    chain_quot_hom, mk'_apply, mk'_apply, QuotientAddGroup.eq, coe_add, coe_add,
    neg_add_rev, add_comm, ← add_assoc, add_neg_cancel_right, ← sub_eq_add_neg
  ]
  exact f_pow_sub_mem_D_Subgroup x₀.prop _

theorem chain_quot_hom_lift_chain_eq_const_zero (hi : i + 1 ≤ D_rank f) :
    chain_quot_chain_hom ∘ (lift_chain' hi) =
    const (D_chain f (D_rank f - i)) 0 := by
  ext x; rw [comp_apply, const_apply, ← hom_lift_chain_eq_zero]; rfl

end

section

variable {i : ℕ} (hi : i ≤ D_rank f)
variable (x₀ : D_chain f (D_rank f - i))

theorem coset_full_play_elim_list_rev_partial {j : ℕ}
    (hj : j < Nat.card (chain_quot f (D_rank f - i))) (k : Fin 2) :
    coset_full_play x₀ (elim_list_rev_partial hi hj k) =
    (chain_quot_chain_hom x₀) - chain_quot_equivFin.symm ⟨j, hj⟩ := by
  rw [coset_full_play, map_cons, sum_cons, sub_eq_add_neg]
  apply congrArg (_ + ·)
  rcases i with _ | _
  · rcases j with _ | _
    · have : (⟨0, hj⟩ : Fin _) = 0 := rfl
      rw [
        this, chain_quot_equivFin_symm_zero_eq_zero, neg_zero,
        elim_list_rev_partial, map_nil, sum_nil
      ]
    rw [
      chain_quot_card_eq_relindex, Nat.sub_zero, ← D_core,
      relindex_eq_one.mpr <| D_core_le_chain _ _, Nat.lt_succ_iff
    ] at hj
    contradiction
  have aa :
      (
        map chain_quot_chain_hom <| map (lift_chain' hi) <|
        elim_list_rev_partial (Nat.le_of_succ_le hi)
        (Nat.pred_lt_self Nat.card_pos) 1
      ).sum = 0 := by
    rw [
      List.map_map, chain_quot_hom_lift_chain_eq_const_zero, List.map_const,
      sum_replicate, smul_zero
    ]
  revert k
  rw [
    Fin.forall_fin_two, elim_list_rev_partial, map_append, sum_append, aa,
    add_zero, and_self
  ]
  induction' j with _ ih
  · have : (⟨0, hj⟩ : Fin _) = 0 := rfl
    rw [
      this, chain_quot_equivFin_symm_zero_eq_zero, neg_zero,
      elim_list_rev_partial, map_nil, sum_nil
    ]
  rw [
    elim_list_rev_partial, elim_list_rev_partial, map_append, map_append,
    sum_append, sum_append, ih, aa, add_zero, map_singleton, sum_singleton,
    chain_elim_map, map_sub, chain_quot_rep,
    surjInv_eq chain_quot_chain_hom_surj, surjInv_eq chain_quot_chain_hom_surj,
    ← add_sub_assoc, add_left_neg, zero_sub
  ]

theorem elim_list_rev_partial_can_shrink (𝒟 : List ℕ) :
    (
      chain_full_play x₀
      (
        elim_list_rev_partial hi
        (chain_quot_equivFin <| chain_quot_chain_hom x₀).prop 0
      ) 𝒟
    ).val ∈ D_chain f (D_rank f - i + 1) := by
  have h : coset_full_play x₀
    (
      elim_list_rev_partial hi
      (chain_quot_equivFin <| chain_quot_chain_hom x₀).prop 0
    ) = 0 := by
      rw [coset_full_play_elim_list_rev_partial, symm_apply_apply, sub_self]
  rw [
    coset_full_play_eq_hom_chain_full_play _ _ 𝒟, chain_quot_chain_hom,
    AddMonoidHom.mk'_apply, Subtype.mk.injEq
  ] at h
  rw [← eq_zero_iff]; convert h

theorem construct_chain_play (𝒟 : List ℕ) :
    ∃ k ≤ (elim_list_rev_partial hi (Nat.pred_lt_self Nat.card_pos) 1).length,
    (
      chain_play x₀ (elim_list_rev_partial hi (Nat.pred_lt_self Nat.card_pos) 1)
      𝒟 k
    ).val ∈ D_core f := by
  induction' i with i ih generalizing 𝒟
  · use 0, Nat.zero_le _
    rw [chain_play]; convert mem x₀
  let hp := (chain_quot_equivFin <| chain_quot_chain_hom x₀).prop
  let xₘ : D_chain f (D_rank f - i) :=
    ⟨
      _, mem_of_subset_of_mem (by rw [rev_rank_of_succ_le hi])
      <| elim_list_rev_partial_can_shrink hi x₀ 𝒟
    ⟩
  rcases
    ih (Nat.le_of_succ_le hi) xₘ (𝒟.drop (elim_list_rev_partial hi hp 0).length)
    with ⟨k, hk, hk'⟩
  have :
      (elim_list_rev_partial hi hp 0).length + k ≤
      (elim_list_rev_partial hi hp 1).length := by
    rw [elim_list_rev_partial, length_append, length_map]
    exact Nat.add_le_add_left hk _
  use
    (elim_list_rev_partial hi hp 0).length + k,
    this.trans <| IsPrefix.length_le <| elim_list_rev_prefix_j hi hp
  rcases elim_list_rev_prefix_j hi hp with ⟨s, hs⟩
  have : chain_full_play x₀ (elim_list_rev_partial hi hp 0) 𝒟 =
      lift_chain' hi xₘ := rfl
  rw [
    ← hs, elim_list_rev_partial, append_assoc, chain_play_concat₂, this,
    chain_play_concat₁ _ _ _ _ <| (length_map _ _).symm ▸ hk,
    ← chain_play_lift'
  ]
  exact hk'

end

theorem construct_play (f : G ≃+ G) (x₀ : G) (𝒟 : List ℕ) :
    ∃ k ≤ (D_core f).index - 1, play f x₀
    (
      (
        elim_list_rev_partial (le_refl D_rank f)
        (Nat.pred_lt_self Nat.card_pos) 1
      ).map val
    ) 𝒟 k ∈ D_core f := by
  let xₘ : D_chain f (D_rank f - D_rank f) :=
    ⟨x₀, by rw [Nat.sub_self]; exact mem_univ _⟩
  rcases construct_chain_play (le_refl D_rank f) xₘ 𝒟 with ⟨k, hk, hk'⟩
  use k, ((@length_elim_list_rev_max_eq_core_index_pred _ _ _ f)  ▸ hk)
  rw [chain_play_eq_play] at hk'; convert hk'

theorem thm_4 (h : D_core f = ⊥) : isAttackWin f := by
  use
    (
      elim_list_rev_partial (le_refl D_rank f)
      (Nat.pred_lt_self Nat.card_pos) 1
    ).map val
  intro x₀ 𝒟; rcases construct_play f x₀ 𝒟 with ⟨n, hn, hn'⟩
  rw [h, index_bot_eq_card] at hn; rw [h, mem_bot] at hn'
  exact ⟨n, hn, hn'⟩
