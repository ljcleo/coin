import Coin.Common

@[ext]
structure Coins (n : ℕ) where
  val : ℕ
  prop : val < 2 ^ n

variable {n : ℕ}

def Coins.eq_of_val_eq {x y : Coins n} (h : x.val = y.val) : x = y := by
  ext; exact h

def Coins.add (x y : Coins n) : Coins n :=
  { val := x.val ^^^ y.val, prop := Nat.xor_lt_two_pow x.prop y.prop }

def Coins.sub (x y : Coins n) : Coins n := x.add y
def Coins.zero : Coins n := { val := 0, prop := Nat.two_pow_pos _ }
def Coins.neg (x : Coins n) : Coins n := x

instance : Add (Coins n) where add := .add
instance : Zero (Coins n) where zero := .zero
instance : Neg (Coins n) where neg := .neg
instance : Sub (Coins n) where sub := .sub

@[simp] theorem Coins.add_eq (x y : Coins n) : x.add y = x + y := rfl
@[simp] theorem Coins.zero_eq : Coins.zero = (0 : Coins n) := rfl
@[simp] theorem Coins.neg_eq (x : Coins n) : x.neg = -x := rfl
@[simp] theorem Coins.sub_eq (x y : Coins n) : x.sub y = x - y := rfl

@[simp]
theorem Coins.val_add (x y : Coins n) : (x + y).val = x.val ^^^ y.val := rfl

@[simp]
theorem Coins.val_sub (x y : Coins n) : (x - y).val = x.val ^^^ y.val := rfl

@[simp] theorem Coins.val_zero : (0 : Coins n).val = 0 := rfl
@[simp] theorem Coins.val_neg (x : Coins n) : (-x).val = x.val := rfl

theorem Coins.add_assoc (x y z : Coins n) : x + y + z = x + (y + z) := by
  apply Coins.eq_of_val_eq
  rw [Coins.val_add, Coins.val_add, Coins.val_add, Coins.val_add, Nat.xor_assoc]

theorem Coins.add_comm (x y : Coins n) : x + y = y + x := by
  apply Coins.eq_of_val_eq; rw [Coins.val_add, Coins.val_add, Nat.xor_comm]

@[simp]
theorem Coins.zero_add (x : Coins n) : 0 + x = x := by
  apply Coins.eq_of_val_eq; rw [Coins.val_add, Coins.val_zero, Nat.zero_xor]

@[simp]
theorem Coins.add_zero (x : Coins n) : x + 0 = x := by
  apply Coins.eq_of_val_eq; rw [Coins.val_add, Coins.val_zero, Nat.xor_zero]

@[simp]
theorem Coins.add_left_neg (x : Coins n) : -x + x = 0 := by
  apply Coins.eq_of_val_eq
  rw [Coins.val_add, Coins.val_neg, Coins.val_zero, Nat.xor_self]

@[simp]
theorem Coins.sub_eq_add_neg (x y : Coins n) : x - y = x + -y := by
  apply Coins.eq_of_val_eq; rw [Coins.val_sub, Coins.val_add, Coins.val_neg]

instance Coins.addCommSemigroup : AddCommSemigroup (Coins n) where
  add_assoc := add_assoc
  add_comm := add_comm

instance Coins.addCommMonoid : AddCommMonoid (Coins n) where
  __ := addCommSemigroup
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

instance Coins.addCommGroup : AddCommGroup (Coins n) where
  __ := Coins.addCommMonoid
  add_left_neg := add_left_neg
  zsmul := zsmulRec

def Coins.equiv_Fin : Coins n ≃ Fin (2 ^ n) where
  toFun := fun x ↦ ⟨x.val, x.prop⟩
  invFun := fun x ↦ { val := x.val, prop := x.prop }
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

instance : Fintype (Coins n) := Fintype.ofEquiv _ (Coins.equiv_Fin).symm
