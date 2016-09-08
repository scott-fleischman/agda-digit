module Basic.NumberNat where

open import Agda.Builtin.Nat
open import Agda.Builtin.FromNat
open import Agda.Builtin.Unit

instance
  NumberNat : Number Nat
  Number.Constraint NumberNat _ = ⊤
  Number.fromNat NumberNat n = n
