import Coin.CoinsBit

def Nat.L (n x : ℕ) : ℕ := x <<< 1 % (2 ^ n) ||| x >>> (n - 1)
def Nat.R (n x : ℕ) : ℕ := x >>> 1 ||| x <<< (n - 1) % (2 ^ n)

section

variable {n : ℕ}

theorem Nat.L_lt_two_pow {x : ℕ} (h : x < 2 ^ n) : n.L x < 2 ^ n :=
  Nat.or_lt_two_pow (Nat.mod_lt _ <| Nat.two_pow_pos _) <|
  lt_of_le_of_lt (Nat.shiftRight_eq_div_pow _ _ ▸ Nat.div_le_self _ _) h

theorem Nat.R_lt_two_pow {x : ℕ} (h : x < 2 ^ n) : n.R x < 2 ^ n :=
  Nat.or_lt_two_pow (lt_of_le_of_lt (Nat.div_le_self _ _) h) <|
  Nat.mod_lt _ <| Nat.two_pow_pos _

def Coins.L (x : Coins n) : Coins n :=
  { val := n.L x.val, prop := Nat.L_lt_two_pow x.prop }

def Coins.R (x : Coins n) : Coins n :=
  { val := n.R x.val, prop := Nat.R_lt_two_pow x.prop }

@[simp] theorem Coins.val_L (x : Coins n) : x.L.val = n.L x.val := rfl
@[simp] theorem Coins.val_R (x : Coins n) : x.R.val = n.R x.val := rfl

theorem Coins.testBit_L (x : Coins n) (m : ℕ) :
    x.L.testBit m = x.testBit (m + n - 1) := by
  rw [testBit, testBit, val_L, Nat.L]
  rcases n with _ | n
  · have : x.val = 0 := Nat.eq_zero_of_le_zero <| Nat.le_of_lt_succ x.prop
    rw [
      this, Nat.zero_shiftLeft, Nat.zero_mod, Nat.or_zero, Nat.zero_shiftRight,
      Nat.zero_testBit, Nat.zero_testBit
    ]
  have h : m % (n + 1) < n + 1 := Nat.mod_lt _ <| Nat.zero_lt_succ _
  rw [
    Nat.testBit_or, Nat.testBit_mod_two_pow, decide_eq_true h, Bool.true_and,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_sub_cancel,
    ← Nat.add_assoc, Nat.add_sub_cancel
  ]
  by_cases h' : m % (n + 1) = 0
  · rw [
      Nat.add_mod, h', decide_eq_false <| (lt_iff_not_ge _ _).mp Nat.zero_lt_one,
      Bool.false_and, Bool.false_or, Nat.add_zero n, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt <| Nat.lt_succ_self _
    ]
  have : 1 ≤ m % (n + 1) := Nat.succ_le_of_lt <| Nat.pos_of_ne_zero h'
  rw [
    decide_eq_true this, Bool.true_and,
    testBit_val_high _ <| Nat.add_le_add_left this _, Bool.or_false,
    ← Nat.mod_add_mod, ← Nat.add_sub_cancel (m % (n + 1) + n) 1,
    Nat.add_assoc, Nat.sub_add_comm this, Nat.add_mod_right,
    Nat.mod_eq_of_lt <| lt_of_le_of_lt (Nat.sub_le _ _) h
  ]

theorem Coins.testBit_R (x : Coins n) (m : ℕ) :
    x.R.testBit m = x.testBit (m + 1) := by
  rw [testBit, testBit, val_R, Nat.R]
  rcases n with _ | n
  · have : x.val = 0 := Nat.eq_zero_of_le_zero <| Nat.le_of_lt_succ x.prop
    rw [
      this, Nat.zero_shiftRight, Nat.or_zero, Nat.zero_shiftLeft, Nat.zero_mod,
      Nat.zero_testBit, Nat.zero_testBit
    ]
  have h : m % (n + 1) < n + 1 := Nat.mod_lt _ <| Nat.zero_lt_succ _
  rw [
    Nat.add_sub_cancel, Nat.testBit_or, Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow, decide_eq_true h, Bool.true_and,
    Nat.testBit_shiftLeft
  ]
  by_cases h' : m % (n + 1) = n
  · rw [
      Nat.add_mod, h', Nat.add_comm 1, testBit_val_high _ <| le_refl _,
      Bool.false_or, decide_eq_true <| le_refl _, Bool.true_and, Nat.sub_self,
    ]
    congr 1; nth_rw 1 [← Nat.mod_eq_of_lt <| Nat.lt_succ_self n]
    rw [← Nat.add_mod, Nat.mod_self]
  have : m % (n + 1) < n := lt_of_le_of_ne (Nat.le_of_lt_succ h) h'
  rw [
    decide_eq_false <| (lt_iff_not_ge _ _).mp this, Bool.false_and,
    Bool.or_false, Nat.add_comm 1, ← Nat.mod_add_mod,
    Nat.mod_eq_of_lt <| Nat.succ_lt_succ this
  ]

theorem Coins.R_L_eq (x : Coins n) : x.L.R = x := by
  apply Coins.eq_of_testBit_eq; intro i
  rw [
    testBit_R, testBit_L, Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc,
    Nat.add_sub_cancel, testBit, testBit, Nat.add_mod_right
  ]

theorem Coins.L_R_eq (x : Coins n) : x.R.L = x := by
  apply Coins.eq_of_testBit_eq; intro i
  rw [testBit_L, testBit_R, testBit, testBit]
  rcases n with _ | n
  · have : x.val = 0 := Nat.eq_zero_of_le_zero <| Nat.le_of_lt_succ x.prop
    rw [this, Nat.zero_testBit, Nat.zero_testBit]
  rw [← Nat.add_assoc, Nat.add_sub_cancel, Nat.add_assoc, Nat.add_mod_right]

@[simp]
theorem Coins.L_add (x y : Coins n) : (x + y).L = x.L + y.L := by
  apply Coins.eq_of_testBit_eq; intro i
  rw [testBit_L, testBit_add, testBit_add, testBit_L, testBit_L]

@[simp]
theorem Coins.R_add (x y : Coins n) : (x + y).R = x.R + y.R := by
  apply Coins.eq_of_testBit_eq; intro i
  rw [testBit_R, testBit_add, testBit_add, testBit_R, testBit_R]

end

variable (n : ℕ)

def Coins.L_equiv : Coins n ≃ Coins n where
  toFun := L
  invFun := R
  left_inv := R_L_eq
  right_inv := L_R_eq

def Coins.R_equiv : Coins n ≃ Coins n where
  toFun := .R
  invFun := .L
  left_inv := L_R_eq
  right_inv := R_L_eq

def Coins.L_addEquiv : Coins n ≃+ Coins n := AddEquiv.mk' (L_equiv _) L_add
def Coins.R_addEquiv : Coins n ≃+ Coins n := AddEquiv.mk' (R_equiv _) R_add
