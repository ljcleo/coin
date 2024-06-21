import Coin.Common

open BitVec Bool Fintype

@[ext]
structure CoinConfig (n : ℕ) where
  ofBitVec ::
  toBitVec : BitVec n

section

variable {n : ℕ}

def CoinConfig.add (x y : CoinConfig n) : CoinConfig n :=
  .ofBitVec (x.toBitVec ^^^ y.toBitVec)

instance CoinConfig.instAdd : Add (CoinConfig n) where add := CoinConfig.add

@[simp]
theorem CoinConfig.add_eq (x y : CoinConfig n) :
    CoinConfig.add x y = x + y := rfl

@[simp]
theorem CoinConfig.toBitVec_add (x y : CoinConfig w) :
    (x + y).toBitVec = x.toBitVec ^^^ y.toBitVec := rfl

theorem CoinConfig.add_assoc (x y z : CoinConfig w) :
    x + y + z = x + (y + z) := by
  ext i
  rw [
    toBitVec_add, toBitVec_add, toBitVec_add, toBitVec_add, getLsb_xor,
    getLsb_xor, getLsb_xor, getLsb_xor, xor_assoc
  ]

theorem CoinConfig.add_comm (x y : CoinConfig w) : x + y = y + x := by
  ext i; rw [toBitVec_add, toBitVec_add, getLsb_xor, getLsb_xor, Bool.xor_comm]

instance CoinConfig.addCommSemigroup : AddCommSemigroup (CoinConfig n) where
  add_assoc := CoinConfig.add_assoc
  add_comm := CoinConfig.add_comm

def CoinConfig.zero : CoinConfig n := .ofBitVec (BitVec.zero _)
instance : Zero (CoinConfig n) where zero := CoinConfig.zero

@[simp]
theorem CoinConfig.zero_eq : CoinConfig.zero = (0 : CoinConfig n) := rfl

@[simp]
theorem CoinConfig.toBitVec_zero : (0 : CoinConfig n).toBitVec = 0#n := rfl

@[simp]
theorem CoinConfig.zero_add (x : CoinConfig n) : 0 + x = x := by
  ext i
  rw [toBitVec_add, toBitVec_zero, getLsb_xor, getLsb_zero, Bool.false_xor]

@[simp]
theorem CoinConfig.add_zero (x : CoinConfig n) : x + 0 = x := by
  ext i
  rw [toBitVec_add, toBitVec_zero, getLsb_xor, getLsb_zero, Bool.xor_false]

instance CoinConfig.addCommMonoid : AddCommMonoid (CoinConfig n) where
  __ := CoinConfig.addCommSemigroup
  zero_add := CoinConfig.zero_add
  add_zero := CoinConfig.add_zero
  nsmul := nsmulRec

def CoinConfig.neg (x : CoinConfig n) : CoinConfig n := x
instance CoinConfig.instNeg : Neg (CoinConfig n) where neg := CoinConfig.neg

@[simp]
theorem CoinConfig.neg_eq (x : CoinConfig n) : CoinConfig.neg x = -x := rfl

@[simp]
theorem CoinConfig.toBitVec_neg (x : CoinConfig n) :
    (-x).toBitVec = x.toBitVec := rfl

@[simp]
theorem CoinConfig.add_left_neg (x : CoinConfig n) : -x + x = 0 := by
  ext i
  rw [
    toBitVec_add, toBitVec_neg, toBitVec_zero, getLsb_xor, getLsb_zero,
    Bool.xor_self
  ]

def CoinConfig.sub (x y : CoinConfig n) : CoinConfig n := x + y
instance CoinConfig.instSub : Sub (CoinConfig n) where sub := CoinConfig.sub

@[simp]
theorem CoinConfig.sub_eq (x y : CoinConfig n) :
    CoinConfig.sub x y = x - y := rfl

@[simp]
theorem CoinConfig.toBitVec_sub (x y : CoinConfig n) :
    (x - y).toBitVec = x.toBitVec ^^^ y.toBitVec := rfl

@[simp]
theorem CoinConfig.sub_eq_add_neg (x y : CoinConfig n) : x - y = x + -y := by
  ext1; rw [toBitVec_sub, toBitVec_add, toBitVec_neg]

instance : AddCommGroup (CoinConfig n) where
  __ := CoinConfig.addCommMonoid
  add_left_neg := CoinConfig.add_left_neg
  zsmul := zsmulRec

def CoinConfig.equiv_Fin : CoinConfig n ≃ Fin (2^n) where
  toFun := toFin ∘ CoinConfig.toBitVec
  invFun := .ofBitVec ∘ ofFin
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

instance : Fintype (CoinConfig n) := ofEquiv _ (CoinConfig.equiv_Fin).symm

end
