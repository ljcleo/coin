import Coin.Coins

variable {n : ℕ}

def Coins.testBit (x : Coins n) (m : ℕ) : Bool := x.val.testBit (m % n)

theorem Coins.val_lt_two_pow_of_lt (x : Coins n)
    {m : ℕ} (h : n ≤ m) : x.val < 2 ^ m :=
  lt_of_lt_of_le x.prop <| Nat.pow_le_pow_of_le Nat.one_lt_two h

theorem Coins.testBit_val_high (x : Coins n)
    {m : ℕ} (h : n ≤ m) : x.val.testBit m = false :=
  Nat.testBit_eq_false_of_lt <| val_lt_two_pow_of_lt _ h

theorem Coins.testBit_eq_mod (x : Coins n) (m : ℕ) :
    x.testBit m = x.testBit (m % n) := by rw [testBit, testBit, Nat.mod_mod]

theorem Coins.testBit_add (x y : Coins n) (m : ℕ) :
    (x + y).testBit m = (x.testBit m).xor (y.testBit m) := by
  rw [testBit, val_add, Nat.testBit_xor, testBit, testBit]

theorem Coins.testBit_sub (x y : Coins n) (m : ℕ) :
    (x - y).testBit m = (x.testBit m).xor (y.testBit m) := by
  rw [testBit, val_sub, Nat.testBit_xor, testBit, testBit]

theorem Coins.zero_testBit (m : ℕ) : (0 : Coins n).testBit m = false := by
  rw [testBit, val_zero, Nat.zero_testBit]

theorem Coins.eq_of_testBit_eq {x y : Coins n}
    (h : ∀ i : ℕ, x.testBit i = y.testBit i) : x = y := by
  refine eq_of_val_eq <| Nat.eq_of_testBit_eq fun i ↦ ?_
  by_cases h' : i < n
  · replace h := h i
    rw [testBit, testBit, Nat.mod_eq_of_lt h'] at h; exact h
  push_neg at h'; rw [Coins.testBit_val_high _ h', Coins.testBit_val_high _ h']
