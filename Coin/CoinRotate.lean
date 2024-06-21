import Coin.CoinConfig

open BitVec

variable {n : ℕ}

def CoinConfig.rotate (x : CoinConfig n) : CoinConfig n :=
  .ofBitVec (x.toBitVec.rotateLeft 1)

theorem CoinConfig.toBitVec_rotate (x : CoinConfig n) :
  x.rotate.toBitVec = (x.toBitVec).rotateLeft 1 := rfl

def CoinConfig.inv_rotate (x : CoinConfig n) : CoinConfig n :=
  .ofBitVec (x.toBitVec.rotateRight 1)

theorem CoinConfig.toBitVec_inv_rotate (x : CoinConfig n) :
  x.inv_rotate.toBitVec = (x.toBitVec).rotateRight 1 := rfl

theorem BitVec.rotate_left_inv (x : BitVec n) :
    (x.rotateLeft 1).rotateRight 1 = x := by
  rw [rotateLeft, rotateRight]
  by_cases h₀ : n = 0
  · subst n; trans 0#0
    · exact of_length_zero
    exact of_length_zero.symm
  replace h₀ : 1 ≤ n := Nat.succ_le_of_lt <| Nat.pos_of_ne_zero h₀
  ext ⟨i, hi⟩
  have h₁ : ¬1 + i < 1 := by push_neg; exact Nat.le_add_right _ _
  have h₂ : i - (n - 1) = 0 := Nat.sub_eq_zero_of_le <| Nat.le_pred_of_lt hi
  have h₃ : i - (n - 1) < 1 := lt_of_eq_of_lt h₂ Nat.zero_lt_one
  have h₄ : i - (n - 1) < n := lt_of_lt_of_le h₃ h₀
  have h₅ : n ≤ n - 1 + (1 + i) := by
    rw [← add_assoc, Nat.sub_add_cancel h₀]; exact Nat.le_add_right _ _
  rw [
    getLsb_or, getLsb_ushiftRight, getLsb_or, getLsb_shiftLeft,
    getLsb_ushiftRight, getLsb_shiftLeft, getLsb_or, getLsb_shiftLeft,
    getLsb_ushiftRight, Fin.val_mk, decide_eq_false h₁, decide_eq_true hi,
    decide_eq_true h₃, decide_eq_true h₄, Bool.not_false, Bool.not_true,
    Bool.and_true, Bool.true_and, Bool.true_and, Bool.false_and, Bool.false_or,
    Nat.add_sub_cancel_left, getLsb_ge _ _ h₅, Bool.or_false
  ]
  by_cases h' : i < n - 1
  · rw [
      decide_eq_true <| Nat.add_lt_of_lt_sub' h', decide_eq_true h',
      Bool.not_true, Bool.true_and, Bool.false_and, Bool.or_false
    ]
  have : i = n - 1 := by
    push_neg at h'; exact eq_of_le_of_le (Nat.le_pred_of_lt hi) h'
  subst i
  have : ¬1 + (n - 1) < n := by rw [Nat.add_sub_cancel' h₀]; exact lt_irrefl _
  rw [
    decide_eq_false this, decide_eq_false <| lt_irrefl _, Bool.not_false,
    Bool.false_and, Bool.false_or, Bool.true_and, Nat.sub_self, Nat.add_zero
  ]

theorem BitVec.rotate_right_inv (x : BitVec n) :
    (x.rotateRight 1).rotateLeft 1 = x := by
  rw [rotateRight, rotateLeft]
  by_cases h₀ : n = 0
  · subst n; trans 0#0
    · exact of_length_zero
    exact of_length_zero.symm
  have h₀' : 1 ≤ n := Nat.succ_le_of_lt <| Nat.pos_of_ne_zero h₀
  ext ⟨i, hi⟩
  have h₁ : i - 1 < n := lt_of_le_of_lt (Nat.pred_le _) hi
  have h₂ : ¬n - 1 + i < n - 1 := by
    push_neg; exact Nat.le_add_right _ _
  have h₃ : i - 1 ≤ n - 1 := Nat.le_pred_of_lt h₁
  have h₄ : n ≤ 1 + (n - 1 + i) := by
    rw [← add_assoc, Nat.add_sub_cancel' h₀']; exact Nat.le_add_right _ _
  rw[
    getLsb_or, getLsb_shiftLeft, getLsb_or, getLsb_ushiftRight,
    getLsb_shiftLeft, getLsb_ushiftRight, getLsb_or, getLsb_ushiftRight,
    getLsb_shiftLeft, Fin.val_mk, decide_eq_true hi, decide_eq_true h₁,
    decide_eq_false h₂, Bool.not_false, Bool.true_and, Bool.true_and,
    Bool.and_true, Nat.sub_eq_zero_of_le h₃, getLsb_ge _ _ h₄, Bool.false_or,
    Nat.add_sub_cancel_left
  ]
  by_cases h' : i = 0
  · subst i
    have : n - 1 < n := Nat.pred_eq_sub_one ▸ Nat.pred_lt h₀
    rw [
      decide_eq_true Nat.zero_lt_one, Nat.zero_sub, Nat.add_zero, Nat.add_zero,
      decide_eq_true this, Bool.not_true, Bool.false_and, Bool.false_or,
      Bool.true_and
    ]
  have h'' : 1 ≤ i := Nat.succ_le_of_lt <| Nat.pos_of_ne_zero h'
  have h'₁ : ¬n - 1 + i < n := by
    contrapose! h'
    exact
      Nat.eq_zero_of_le_zero <| Nat.sub_self _ ▸
      (Nat.le_sub_of_add_le' <| Nat.pred_eq_sub_one ▸ Nat.le_pred_of_lt h')
  rw [
    decide_eq_false <| not_lt_of_le h'', decide_eq_false h'₁,
    decide_eq_true <| Nat.pred_eq_sub_one ▸ Nat.pred_lt_pred h' hi,
    Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
    Bool.false_and, Bool.or_false, Bool.or_false, Nat.add_sub_cancel' h''
  ]

theorem CoinConfig.rotate_left_inv (x : CoinConfig n) :
    x.rotate.inv_rotate = x := by
  ext1
  rw [
    CoinConfig.toBitVec_inv_rotate, CoinConfig.toBitVec_rotate,
    BitVec.rotate_left_inv
  ]

theorem CoinConfig.rotate_right_inv (x : CoinConfig n) :
    x.inv_rotate.rotate = x := by
  ext1
  rw [
    CoinConfig.toBitVec_rotate, CoinConfig.toBitVec_inv_rotate,
    BitVec.rotate_right_inv
  ]

def CoinConfig.rotate_equiv : CoinConfig n ≃ CoinConfig n where
  toFun := rotate
  invFun := inv_rotate
  left_inv := rotate_left_inv
  right_inv := rotate_right_inv

def CoinConfig.rotate_addEquiv : CoinConfig n ≃+ CoinConfig n :=
  AddEquiv.mk' rotate_equiv fun x y ↦ by
    ext ⟨i, hi⟩; dsimp [rotate_equiv, rotate]
    rw [
      rotateLeft, rotateLeft, rotateLeft, getLsb_or, getLsb_shiftLeft,
      getLsb_xor, getLsb_ushiftRight, getLsb_xor, getLsb_xor, getLsb_or,
      getLsb_shiftLeft, getLsb_ushiftRight, getLsb_or, getLsb_shiftLeft,
      getLsb_ushiftRight, decide_eq_true hi, Bool.true_and
    ]
    by_cases h : i < 1
    · rw [
        decide_eq_true h, Bool.not_true, Bool.false_and, Bool.false_or,
        Bool.false_and, Bool.false_or, Bool.false_and, Bool.false_or
      ]
    have : n ≤ n - 1 + i := by
      push_neg at h; exact Nat.le_add_of_sub_le <| Nat.sub_le_sub_left h _
    rw [
      decide_eq_false h, Bool.not_false, Bool.true_and, Bool.true_and,
      Bool.true_and, getLsb_ge _ _ this, getLsb_ge _ _ this, Bool.false_xor,
      Bool.or_false, Bool.or_false, Bool.or_false
    ]
