import Coin.ChainInf

open AddAction AddAut AddSubgroup Set

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def elem_rank_unique (f : G ≃+ G) (x : G) :
    Unique { a // isChainInf f x a } :=
  Classical.choice <| (unique_subtype_iff_exists_unique _).mpr <|
  chain_inf_exists_unique _ _

noncomputable def elem_rank (f : G ≃+ G) (x : G) : ℕ :=
  (elem_rank_unique f x).default

theorem elem_rank_is_chain_inf (f : G ≃+ G) (x : G) :
    isChainInf f x <| elem_rank f x :=
  (elem_rank_unique _ _).toInhabited.default.property

theorem elem_rank_le_rank (f : G ≃+ G) (x : G) : elem_rank f x ≤ D_rank f :=
  chain_inf_le_rank <| elem_rank_is_chain_inf _ _

theorem eq_elem_rank_of_is_chain_inf {f : G ≃+ G} {x : G} {i : ℕ}
    (h : isChainInf f x i) : i = elem_rank f x :=
  (chain_inf_exists_unique _ _).unique h (elem_rank_is_chain_inf _ _)

theorem le_elem_rank_of_le_rank_of_mem_chain {f : G ≃+ G} {x : G} {i : ℕ}
    (hi : i ≤ D_rank f) (h : x ∈ D_chain f i) : i ≤ elem_rank f x :=
  le_chain_inf_of_le_rank_of_mem_chain (elem_rank_is_chain_inf _ _) hi h

theorem quot_map_f_pow_eq_quot_map' {f : G ≃+ G} (x : G) (i : ℕ) :
    QuotientAddGroup.mk' (D_chain f (elem_rank f x + 1)) ((f ^ i) x) =
    QuotientAddGroup.mk' (D_chain f (elem_rank f x + 1)) x :=
  quot_map_f_pow_eq_quot_map (elem_rank_is_chain_inf _ _).mem i

theorem elem_rank_eq_of_quot_map_eq {f : G ≃+ G} {x y : G}
    (
      h : QuotientAddGroup.mk' (D_chain f (elem_rank f x + 1)) x =
      QuotientAddGroup.mk' (D_chain f (elem_rank f x + 1)) y
    ) : elem_rank f x = elem_rank f y := by
  apply QuotientAddGroup.eq.mp at h
  exact
    eq_elem_rank_of_is_chain_inf
    ⟨
      (add_mem_cancel_left <| neg_mem (elem_rank_is_chain_inf _ _).mem).mp <|
      mem_of_subset_of_mem (D_chain_adj_le _ <| elem_rank _ _) h,
      fun h' ↦
        (elem_rank_is_chain_inf _ _).succ <|
        neg_neg x ▸ neg_mem <| (add_mem_cancel_right h').mp h
    ⟩

theorem elem_rank_eq_of_quot_map_eq' {f : G ≃+ G} {x y : G}
    (
      h : QuotientAddGroup.mk' (D_chain f (elem_rank f y + 1)) x =
      QuotientAddGroup.mk' (D_chain f (elem_rank f y + 1)) y
    ) : elem_rank f x = elem_rank f y :=
  (elem_rank_eq_of_quot_map_eq h.symm).symm

theorem elem_rank_f_pow_eq (f : G ≃+ G) {x : G} (i : ℕ) :
    elem_rank f ((f ^ i) x) = elem_rank f x :=
  elem_rank_eq_of_quot_map_eq' <| quot_map_f_pow_eq_quot_map' _ _

theorem add_eq_elem_rank_left_of_elem_rank_lt {f : G ≃+ G} {x y : G}
    (h : elem_rank f x < elem_rank f y) :
    elem_rank f (x + y) = elem_rank f x :=
  (
    eq_elem_rank_of_is_chain_inf
    ⟨
      add_mem (elem_rank_is_chain_inf _ _).mem <|
      mem_of_subset_of_mem (D_chain_le_of_le _ <| le_of_lt h)
      (elem_rank_is_chain_inf _ _).mem,
      fun h' ↦
        (elem_rank_is_chain_inf _ _).succ <|
        (
          add_mem_cancel_right <|
          mem_of_subset_of_mem (D_chain_le_of_le _ <| Nat.succ_le_of_lt h)
          (elem_rank_is_chain_inf _ _).mem
        ).mp h'
    ⟩
  ).symm

theorem elem_rank_le_add_of_elem_rank_eq {f : G ≃+ G} {x y : G}
    (h : elem_rank f x = elem_rank f y) :
    elem_rank f x ≤ elem_rank f (x + y) :=
  le_elem_rank_of_le_rank_of_mem_chain (elem_rank_le_rank _ _) <|
  add_mem (elem_rank_is_chain_inf _ _).mem <|
  h ▸ (elem_rank_is_chain_inf _ _).mem

example {f : G ≃+ G} {x y : G} (hx : elem_rank f x < D_rank f)
    (hxy : elem_rank f x = elem_rank f y)
    (
      h : QuotientAddGroup.mk' (D_chain f (elem_rank f x + 1)) x =
      -(QuotientAddGroup.mk' (D_chain f (elem_rank f x + 1)) y)
    ) : elem_rank f x < elem_rank f (x + y) := by
  apply lt_of_le_of_ne <| elem_rank_le_add_of_elem_rank_eq hxy
  symm; by_contra! h'
  exact
    ne_of_lt hx <| (h' ▸ (elem_rank_is_chain_inf _ _).succ) <|
    neg_neg (x + y) ▸ neg_mem <| (neg_add x _).symm ▸ QuotientAddGroup.eq.mp h

example {f : G ≃+ G} {x y : G} (h : elem_rank f x < elem_rank f (x + y)) :
    elem_rank f x < D_rank f := lt_of_lt_of_le h <| elem_rank_le_rank _ _

example {f : G ≃+ G} {x y : G} (h : elem_rank f x < elem_rank f (x + y)) :
    elem_rank f x = elem_rank f y := by
  contrapose! h
  by_cases h' : elem_rank f x < elem_rank f y
  · exact le_of_eq <| add_eq_elem_rank_left_of_elem_rank_lt h'
  push_neg at h'; replace h' := lt_of_le_of_ne h' h.symm
  exact
    le_of_lt <| add_comm _ x ▸ add_eq_elem_rank_left_of_elem_rank_lt h' ▸ h'

example {f : G ≃+ G} {x y : G} (h : elem_rank f x < elem_rank f (x + y)) :
    QuotientAddGroup.mk' (D_chain f (elem_rank f x + 1)) x =
    -(QuotientAddGroup.mk' (D_chain f (elem_rank f x + 1)) y) :=
  QuotientAddGroup.eq.mpr <| neg_add x _ ▸ neg_mem <|
  mem_of_subset_of_mem (D_chain_le_of_le _ (Nat.succ_le_of_lt h))
  (elem_rank_is_chain_inf _ _).mem
