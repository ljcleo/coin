import Coin.CoinsLR
import Coin.CoinsRoller
import Coin.D

open Coins Function

variable {n : ℕ}
variable (x : Coins n)
variable (m k : ℕ)

theorem D_pow_R_testBit_eq_roller :
    ((D (R_addEquiv n))^[k] x).testBit m = roller x m k := by
  induction' k with k ih generalizing m
  · rw [roller_zero]; rfl
  rw [iterate_succ_apply']; nth_rw 1 [D]; dsimp; nth_rw 1 [R_addEquiv]
  dsimp [AddEquiv.mk', R_equiv]
  rw [testBit_sub, testBit_R, ih, ih, roller_succ, Bool.xor_comm']
