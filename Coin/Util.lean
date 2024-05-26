import Coin.Common

open AddSubgroup Set SetLike Unique

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem subgroup_ncard_lt_ncard_of_lt {H₁ H₂ : AddSubgroup G} (h : H₁ < H₂) :
    H₁.carrier.ncard < H₂.carrier.ncard := ncard_lt_ncard h (toFinite _)
