import Coin.CoinsD
import Coin.Final

variable {n : ℕ}

theorem Coins.thm_1 (h : n = 0 ∨ ∃ k : ℕ, n = 2 ^ k) :
    isAttackWin (R_addEquiv n) := by
  refine (final_thm_3 _).mpr fun x ↦ ⟨n, ?_⟩
  rcases h with h | h
  · subst n; convert iterate_map_zero (D (R_addEquiv 0)) _; ext; rw [val_zero]
    exact Nat.eq_zero_of_le_zero <| Nat.le_of_lt_succ x.prop
  rcases h with ⟨k, h⟩; subst n; apply eq_of_testBit_eq; intro i
  rw [zero_testBit, D_pow_R_testBit_eq_roller, roller_two_pow, testBit_eq_mod]
  nth_rw 2 [testBit_eq_mod]; rw [Nat.add_mod_right]; exact Bool.xor_self _

theorem Coins.thm_2 (h : isAttackWin (R_addEquiv n)) :
    n = 0 ∨ ∃ k : ℕ, n = 2 ^ k := by
  contrapose! h; rw [final_thm_3 _]; push_neg; rcases h with ⟨hn, h⟩
  use
    ⟨
      1,
      lt_of_le_of_lt (by norm_num) <| Nat.pow_lt_pow_of_lt (by norm_num) <|
      Nat.pos_of_ne_zero hn
    ⟩
  apply D_pow_ne_zero_of_loop
  let q : ℕ := n / 2 ^ (padicValNat 2 n)
  have hq₀ : n = q * 2 ^ (padicValNat 2 n) :=
    ((Nat.dvd_iff_div_mul_eq _ _).mp pow_padicValNat_dvd).symm
  have hq₁ : 1 < q := by
    contrapose! h
    rcases q with _ | q
    · rw [Nat.zero_mul] at hq₀; contradiction
    rw [eq_of_le_of_le h <| Nat.succ_le_of_lt Nat.succ_pos', Nat.one_mul] at hq₀
    exact ⟨_, hq₀⟩
  have hq₂ : ¬2 ∣ q := by
    have : padicValNat 2 q = 0 := by
      rw [padicValNat.div_pow pow_padicValNat_dvd, Nat.sub_self]
    rw [← Nat.pow_one 2, ← Nat.zero_add 1, ← this]
    apply
      pow_succ_padicValNat_not_dvd (ne_of_lt <| Nat.zero_lt_one.trans hq₁).symm
  have hn₁ : 2 ^ (padicValNat 2 n) < n := by
    nth_rw 2 [hq₀]
    exact (Nat.lt_mul_iff_one_lt_left <| Nat.two_pow_pos _).mpr hq₁
  rcases euler_thm hq₁ hq₂ with ⟨a, ha₀, ha₁⟩
  have ha₂ : 2 ^ padicValNat 2 n < 2 ^ (a + padicValNat 2 n) :=
    Nat.pow_lt_pow_of_lt (by norm_num) <| Nat.lt_add_of_pos_left ha₀
  let d : ℕ := 2 ^ (a + padicValNat 2 n) - 2 ^ padicValNat 2 n
  have hd₀ : 2 ^ (a + padicValNat 2 n) = d + 2 ^ padicValNat 2 n :=
    (Nat.sub_add_cancel <| le_of_lt ha₂).symm
  use 2 ^ padicValNat 2 n, d, Nat.sub_pos_of_lt ha₂
  constructor
  · by_contra! h'; apply congrArg (Coins.testBit · 0) at h'
    rw [D_pow_R_testBit_eq_roller, roller_two_pow, testBit, zero_testBit] at h'
    dsimp [testBit] at h'
    rw [
      Nat.zero_mod, Nat.testBit_one_zero, Nat.zero_add, Nat.mod_eq_of_lt hn₁,
      Bool.true_xor', Bool.not_eq_false'
    ] at h'
    linarith [
      lt_of_lt_of_le
      (Nat.pow_lt_pow_of_lt (by norm_num) <| Nat.two_pow_pos _) <|
      Nat.testBit_implies_ge h'
    ]
  have h' : 2 ^ (a + padicValNat 2 n) % n = 2 ^ padicValNat 2 n:= by
    nth_rw 2 [hq₀]; rw [pow_add, Nat.mul_mod_mul_right, ha₁, Nat.one_mul]
  apply eq_of_testBit_eq; intro i
  rw [
    D_pow_R_testBit_eq_roller, D_pow_R_testBit_eq_roller, ← hd₀,
    roller_two_pow, roller_two_pow
  ]
  congr 1
  rw [testBit, Nat.add_mod, h']; nth_rw 1 [← Nat.mod_eq_of_lt hn₁]
  rw [testBit, ← Nat.add_mod]

theorem Coins.final_thm :
    isAttackWin (R_addEquiv n) ↔ n = 0 ∨ ∃ k : ℕ, n = 2 ^ k :=
  ⟨Coins.thm_2, Coins.thm_1⟩
