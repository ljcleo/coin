import Coin.DCore
import Coin.ChainQuot

open AddSubgroup Fin Fintype List Set SetLike

variable {G : Type*} [Fintype G] [AddCommGroup G]
variable {f : G ≃+ G}

theorem relindex_pos (H K : AddSubgroup G) : 1 ≤ H.relindex K := by
  have hK : Fintype K := Fintype.ofFinite _
  refine
    Nat.succ_le_of_lt <| lt_of_le_of_ne (Nat.zero_le _)
    (
      ne_zero_of_dvd_ne_zero ?_ <|
      relindex_dvd_of_le_left K bot_le
    ).symm
  rw [relindex_bot_left, Nat.card_eq_fintype_card]
  exact
    ne_zero_of_dvd_ne_zero ((@card_top G _ _) ▸ card_ne_zero) <|
    card_dvd_of_le le_top

noncomputable def chain_elim_map (f : G ≃+ G) (i : ℕ) {j : ℕ}
    (h : j < Nat.card (chain_quot f i) - 1) : D_chain f i :=
  chain_quot_rep (chain_quot_equivFin.symm ⟨j, Nat.lt_of_lt_pred h⟩) -
  chain_quot_rep (chain_quot_equivFin.symm ⟨j + 1, Nat.succ_lt_of_lt_pred h⟩)

section

variable {i : ℕ} (hi : i + 1 ≤ D_rank f)

theorem rev_rank_of_succ_le : D_rank f - (i + 1) + 1 = D_rank f - i := by
  rw [← Nat.sub_sub, Nat.sub_add_cancel <| Nat.le_sub_of_add_le' hi]

theorem rev_rank_convert (x : G) :
    x ∈ D_chain f (D_rank f - (i + 1) + 1) ↔ x ∈ D_chain f (D_rank f - i) := by
  rw [rev_rank_of_succ_le hi]

def lift_chain' (x : D_chain f (D_rank f - i)) :
    D_chain f (D_rank f - (i + 1)) :=
  lift_chain <| ⟨x.val, (rev_rank_convert hi _).mpr x.prop⟩

end

noncomputable def elim_list_rev_partial {i : ℕ} (hi : i ≤ D_rank f) {j : ℕ}
    (h : j < Nat.card (chain_quot f (D_rank f - i))) (k : Fin 2) :
    List (D_chain f (D_rank f - i)) :=
  match i, j, k with
    | 0, _, _ => []
    | _ + 1, 0, 0 => []
    | i' + 1, j' + 1, 0 =>
        elim_list_rev_partial hi (Nat.lt_of_succ_lt h) 1 ++
        [chain_elim_map f (D_rank f - (i' + 1)) <| Nat.lt_pred_of_succ_lt h]
    | i' + 1, _, 1 =>
        elim_list_rev_partial hi h 0 ++
        (
          map (lift_chain' hi) <| elim_list_rev_partial (Nat.le_of_succ_le hi)
          (Nat.pred_lt_self Nat.card_pos) 1
        )

section

variable {i : ℕ} (hi : i ≤ D_rank f)

theorem elim_list_rev_adj_j_prefix {j : ℕ}
    (hj : j + 1 < Nat.card (chain_quot f (D_rank f - i))) :
    elim_list_rev_partial hi ((Nat.lt_succ_self _).trans hj) 1 <+:
    elim_list_rev_partial hi hj 1 := by
  rcases i with _ | _
  · rw [elim_list_rev_partial]; exact nil_prefix _
  rw [
    elim_list_rev_partial, elim_list_rev_partial, elim_list_rev_partial,
    elim_list_rev_partial, List.append_assoc
  ]
  exact prefix_append _ _

theorem elim_list_rev_succ_j_prefix {j z : ℕ}
    (hj : j + z < Nat.card (chain_quot f (D_rank f - i))) :
    elim_list_rev_partial hi (lt_of_le_of_lt (Nat.sub_le _ z) hj) 1 <+:
    elim_list_rev_partial hi hj 1 := by
  induction' z with z ih
  · convert prefix_rfl
  rw [Nat.add_succ] at hj
  convert
    (ih <| Nat.lt_of_succ_lt hj).trans <| elim_list_rev_adj_j_prefix hi hj
    using 2
  rw [Nat.add_sub_cancel_right, Nat.add_sub_cancel_right]

theorem elim_list_rev_prefix_of_le {j j' : ℕ}
    (hj : j < Nat.card (chain_quot f (D_rank f - i)))
    (hj' : j' < Nat.card (chain_quot f (D_rank f - i))) (h : j ≤ j') :
    elim_list_rev_partial hi hj 1 <+: elim_list_rev_partial hi hj' 1 := by
  convert elim_list_rev_succ_j_prefix hi <| (Nat.add_sub_cancel' h).symm ▸ hj'
  · rw [Nat.add_sub_cancel_right]
  rw [← Nat.add_sub_assoc h, Nat.add_sub_cancel_left]

theorem elim_list_rev_prefix_j {j : ℕ}
    (hj : j < Nat.card (chain_quot f (D_rank f - i))) :
    elim_list_rev_partial hi hj 1 <+:
    elim_list_rev_partial hi (Nat.pred_lt_self Nat.card_pos) 1 :=
  elim_list_rev_prefix_of_le _ _ _ <| Nat.le_pred_of_lt hj

end

section

variable {i : ℕ} (hi : i ≤ D_rank f)
variable {j : ℕ} (hj : j < Nat.card (chain_quot f (D_rank f - i)))
variable (k : Fin 2)

theorem length_elim_list_rev_partial : (elim_list_rev_partial hi hj k).length =
    (D_core f).relindex (D_chain f (D_rank f - i + 1)) * (j + k) - k := by
  induction' i with i ih generalizing j k
  · rw [elim_list_rev_partial, length_nil, Nat.sub_zero, D_core]
    rw [Nat.sub_zero, chain_quot_card_eq_relindex] at hj
    rw [(D_rank_is_bound f).succ, relindex_self] at *
    rw [one_mul, Nat.add_sub_cancel_right, Nat.lt_one_iff.mp hj]
  have h₁ : D_rank f - (i + 1) + 1 = D_rank f - i := by
    rw [← Nat.sub_sub, Nat.sub_add_cancel <| Nat.le_sub_of_add_le' hi]
  have h₂ :
      (
        elim_list_rev_partial (Nat.le_of_succ_le hi)
        (Nat.pred_lt_self Nat.card_pos) 1
      ).length =
      (D_core f).relindex (D_chain f (D_rank f - i)) - 1 := by
    rw [
      ih (Nat.le_of_succ_le hi) _, Nat.pred_eq_sub_one, val_one,
      Nat.sub_add_cancel Nat.card_pos, chain_quot_card_eq_relindex,
      relindex_mul_relindex _ _ _ (D_core_le_chain _ _) (D_chain_adj_le _ _)
    ]
  revert k
  rw [
    forall_fin_two, val_zero, val_one, add_zero, Nat.sub_zero,
    elim_list_rev_partial, length_append, length_map, h₁, h₂,
    ← Nat.add_sub_assoc <| relindex_pos _ _,
    Nat.sub_eq_iff_eq_add <| (relindex_pos _ _).trans <| Nat.le_add_left _ _,
    Nat.sub_add_cancel <| Nat.mul_pos (relindex_pos _ _) <| Nat.succ_pos _,
    Nat.mul_succ, Nat.add_left_inj, and_self
  ]
  induction' j with j ih'
  · rfl
  rw [
    elim_list_rev_partial, elim_list_rev_partial, length_append, length_append,
    length_singleton, length_map, ih', h₂,
    ← Nat.add_sub_assoc <| relindex_pos _ _, ← Nat.mul_succ,
    Nat.sub_add_cancel <| Nat.mul_pos (relindex_pos _ _) <| Nat.succ_pos _
  ]

theorem length_elim_list_rev_eq_relindex :
    (elim_list_rev_partial hi (Nat.pred_lt_self Nat.card_pos) 1).length =
    (D_core f).relindex (D_chain f (D_rank f - i)) - 1 := by
  rw [
    length_elim_list_rev_partial hi, val_one,
    Nat.pred_eq_sub_one, Nat.sub_add_cancel Nat.card_pos,
    chain_quot_card_eq_relindex,
    relindex_mul_relindex _ _ _ (D_core_le_chain _ _) (D_chain_adj_le _ _)
  ]

theorem length_elim_list_rev_max_eq_core_index_pred :
    (
      elim_list_rev_partial (le_refl D_rank f) (Nat.pred_lt_self Nat.card_pos) 1
    ).length = (D_core f).index - 1 := by
  rw [length_elim_list_rev_eq_relindex, Nat.sub_self]
  dsimp [D_chain, D_chain']; rw [relindex_top_right]

end
