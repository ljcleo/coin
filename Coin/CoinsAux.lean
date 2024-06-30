import Coin.Common

theorem Bool.true_xor' (a : Bool) : true.xor a = !a := Bool.true_xor _

theorem Bool.xor_assoc' (a b c : Bool) : (a.xor b).xor c = a.xor (b.xor c) :=
  Bool.xor_assoc _ _ _

theorem Bool.xor_comm' (a b : Bool) : a.xor b = b.xor a := Bool.xor_comm _ _

theorem decide_sum_odd (a b : ℕ) : (decide ((a + b) % 2 = 1)) =
    (decide (a % 2 = 1)).xor (decide (b % 2 = 1)) := by
  rw [Nat.add_mod]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · rw [ha, Nat.zero_add, Nat.mod_mod, decide_eq_false <| Nat.zero_ne_one]
    exact (Bool.false_xor _).symm
  rw [ha, decide_eq_true <| Eq.refl _]
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> (rw [hb]; norm_num)

theorem padicValNat_le_padicValNat_sub (n : ℕ) {m : ℕ} (h : m < 2 ^ n) :
    padicValNat 2 m ≤ padicValNat 2 (2 ^ n - m)  := by
  by_cases hm : m = 0
  · subst m; exact Nat.zero_le _
  rw [← padicValNat_dvd_iff_le <| (ne_of_lt <| Nat.sub_pos_of_lt h).symm]
  have h' : 2 ^ padicValNat 2 m ∣ m := pow_padicValNat_dvd
  refine Nat.dvd_sub (le_of_lt h) (Nat.pow_dvd_pow _ ?_) h'
  by_contra! h''
  linarith [
    lt_of_lt_of_le (Nat.pow_lt_pow_of_lt Nat.one_lt_two h'') <|
    Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h'
  ]

theorem sub_padicValNat_eq {n m : ℕ} (hm : 0 < m) (h : m < 2 ^ n) :
    padicValNat 2 (2 ^ n - m) = padicValNat 2 m := by
  refine eq_of_le_of_le ?_ (padicValNat_le_padicValNat_sub _ h)
  convert padicValNat_le_padicValNat_sub n <| Nat.sub_lt_self hm <| le_of_lt h
  exact Nat.eq_sub_of_add_eq <| Nat.add_sub_cancel' <| le_of_lt h

theorem Nat.choose_two_pow_pred (n m : ℕ) :
    (2 ^ n - 1).choose m % 2 = if m ≤ 2 ^ n - 1 then 1 else 0 := by
  by_cases h : m ≤ 2 ^ n - 1
  · rw [if_pos h]
    induction' m with m ih
    · norm_num
    replace ih := ih <| Nat.le_of_succ_le h
    have hc : (2 ^ n - 1).choose m ≠ 0 := by
      contrapose! h; rw [Nat.choose_eq_zero_iff] at h
      exact Nat.lt_succ_of_lt h
    have hc' : (2 ^ n - 1).choose (m + 1) ≠ 0 := by
      contrapose! h; rw [Nat.choose_eq_zero_iff] at h; exact h
    have h₁ : padicValNat 2 ((2 ^ n - 1).choose (m + 1)) =
        padicValNat 2 ((2 ^ n - 1).choose m) := by
      apply @Nat.add_right_cancel _ (padicValNat 2 (m + 1))
      rw [
        ← padicValNat.mul hc' <| Nat.succ_ne_zero _, Nat.choose_succ_right_eq,
        padicValNat.mul hc
        (
          ne_of_lt <| Nat.lt_of_succ_le <|
          Nat.le_sub_of_add_le (Nat.add_comm _ 1 ▸ h)
        ).symm
      ]
      congr 1; rw [Nat.sub_sub, Nat.add_comm]
      exact
        sub_padicValNat_eq (Nat.succ_pos _) <|
        Nat.lt_of_le_pred (Nat.two_pow_pos _) h
    have h₂ {a : ℕ} (ha : a ≠ 0) : a % 2 = 1 ↔ padicValNat 2 a = 0 := by
      rw [padicValNat.eq_zero_iff]
      constructor
      · intro h'; right; right
        rw [Nat.dvd_iff_mod_eq_zero, h']; norm_num
      rintro (h' | h' | h')
      · contradiction
      · contradiction
      rcases Nat.mod_two_eq_zero_or_one a with h'' | h''
      · rw [Nat.dvd_iff_mod_eq_zero] at h'; contradiction
      exact h''
    rw [h₂ hc', h₁, ← h₂ hc]; exact ih
  rw [if_neg h, Nat.choose_eq_zero_of_lt <| (lt_iff_not_ge _ _).mpr h]

theorem Nat.choose_two_pow (n m : ℕ) :
    (2 ^ n).choose m % 2 = if m = 0 ∨ m = 2 ^ n then 1 else 0 := by
  rcases m with _ | m
  · norm_num
  nth_rw 1 [← Nat.sub_add_cancel <| Nat.pow_pos <| Nat.zero_lt_two]
  rw [
    Nat.choose_succ_succ', Nat.add_mod, Nat.choose_two_pow_pred,
    Nat.choose_two_pow_pred
  ]
  by_cases h : m + 1 ≤ 2 ^ n - 1
  · rw [
      if_pos <| Nat.le_of_succ_le h, if_pos h, (by norm_num : (1 + 1) % 2 = 0),
      if_neg
    ]
    push_neg
    exact
      ⟨Nat.succ_ne_zero _, ne_of_lt <| Nat.lt_of_le_pred (Nat.two_pow_pos _) h⟩
  rw [if_neg h, Nat.add_zero]; push_neg at h
  by_cases h' : m ≤ 2 ^ n - 1
  · rw [if_pos h', if_pos]; right
    exact
      eq_of_le_of_le (Nat.add_le_of_le_sub (Nat.two_pow_pos _) h') <|
      Nat.le_of_pred_lt h
  rw [if_neg h', if_neg]; push_neg; refine ⟨Nat.succ_ne_zero _, ?_⟩
  contrapose! h'; rw [← h', Nat.add_sub_cancel]

theorem euler_thm {n : ℕ} (hn : 1 < n) (h : ¬2 ∣ n) :
    ∃ a : ℕ, 0 < a ∧ 2 ^ a % n = 1 := by
  use n.totient, Nat.totient_pos.mpr <| Nat.zero_lt_one.trans hn
  refine Nat.mod_eq_of_modEq (Nat.ModEq.pow_totient ?_) hn
  rw [Nat.coprime_two_left]; contrapose! h
  rw [← Nat.even_iff_not_odd, even_iff_two_dvd] at h; exact h
