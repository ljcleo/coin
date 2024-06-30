import Coin.CoinsAux
import Coin.CoinsBit

open Coins Function

variable {n : ℕ}
variable (x : Coins n)
variable (m k : ℕ)

def gated_testBit (i : ℕ) : Bool :=
  decide ((k.choose i) % 2 = 1) && x.testBit (m + i)

theorem gated_testBit_zero : gated_testBit x m k 0 = x.testBit m := by
  rw [gated_testBit, decide_eq_true <| by norm_num]; rfl

def gated_fold (i : ℕ) (z : Bool) : Bool := z.xor <| gated_testBit x m k (i + 1)
def roller : Bool := Nat.fold (gated_fold x m k) k <| gated_testBit x m k 0

theorem roller_zero : roller x m 0 = x.testBit m := by
  rw [roller, Nat.fold, gated_testBit_zero]

def partial_roller (i : ℕ) : Bool :=
  Nat.fold (gated_fold x m k) i <| gated_testBit x m k 0

theorem partial_roller_zero : partial_roller x m k 0 = x.testBit m := by
  rw [partial_roller, Nat.fold, gated_testBit_zero]

theorem partial_roller_succ (i : ℕ) : partial_roller x m k (i + 1) =
    (partial_roller x m k i).xor (gated_testBit x m k (i + 1)) := rfl

theorem roller_eq_partial : roller x m k = partial_roller x m k k := rfl

theorem partial_roller_two_pow {i : ℕ} (h : i < 2 ^ k) :
    partial_roller x m (2 ^ k) i = x.testBit m := by
  induction' i with i ih
  · exact partial_roller_zero _ _ _
  have : (2 ^ k).choose (i + 1) % 2 = 0 := by
    rw [Nat.choose_two_pow, if_neg]; push_neg
    exact ⟨Nat.succ_ne_zero _, ne_of_lt h⟩
  rw [
    partial_roller_succ, ih <| Nat.lt_of_succ_lt h, gated_testBit, this,
    decide_eq_false (by norm_num), Bool.false_and
  ]
  exact Bool.xor_false _

theorem roller_two_pow :
    roller x m (2 ^ k) = (x.testBit m).xor (x.testBit (m + 2 ^ k)) := by
  rw [roller_eq_partial]
  let w : ℕ := 2 ^ k - 1
  have hw : w + 1 = 2 ^ k := by
    rw [Nat.sub_add_cancel <| Nat.pow_pos <| Nat.zero_lt_two]
  have hw' : w < 2 ^ k := by rw [← hw]; exact Nat.lt_succ_self _
  nth_rw 2 [← hw]
  rw [
    partial_roller_succ, partial_roller_two_pow _ _ _ hw', gated_testBit, hw,
    Nat.choose_self, decide_eq_true (by norm_num), Bool.true_and
  ]

theorem partial_roller_merge (i : ℕ) :
    (partial_roller x m k (i + 1)).xor (partial_roller x (m + 1) k i) =
    partial_roller x m (k + 1) (i + 1) := by
  induction' i with _ ih generalizing m
  · rw [
      partial_roller_succ, partial_roller_succ, partial_roller_zero,
      partial_roller_zero, partial_roller_zero, Bool.xor_assoc',
      gated_testBit, gated_testBit, Nat.choose_succ_succ, decide_sum_odd,
      Bool.and_xor_distrib_right, Bool.xor_comm,
      decide_eq_true <| (by norm_num : k.choose 0 % 2 = 1), Bool.true_and
    ]
  rw [partial_roller_succ]; nth_rw 2 [partial_roller_succ]
  nth_rw 2 [partial_roller_succ]; rw [Bool.xor_assoc']
  nth_rw 2 [← Bool.xor_assoc']; nth_rw 3 [Bool.xor_comm']
  rw [Bool.xor_assoc']; nth_rw 1 [← Bool.xor_assoc']
  rw [
    ih, gated_testBit, gated_testBit, gated_testBit, Nat.choose_succ_succ,
    decide_sum_odd, Bool.and_xor_distrib_right, Bool.xor_comm
  ]
  congr 4; rw [Nat.add_assoc, Nat.add_comm 1]

theorem roller_succ :
    roller x m (k + 1) = (roller x m k).xor (roller x (m + 1) k) := by
  rw [
    roller_eq_partial, roller_eq_partial, roller_eq_partial,
    ← partial_roller_merge, partial_roller_succ, gated_testBit,
    Nat.choose_eq_zero_iff.mpr <| Nat.lt_succ_self _,
    decide_eq_false (by norm_num), Bool.false_and
  ]
  congr; exact Bool.xor_false _
