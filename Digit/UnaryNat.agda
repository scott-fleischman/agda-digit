module Digit.UnaryNat where

open import Agda.Builtin.FromNat
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

instance
  NumberUnaryNat : Number Nat
  Number.Constraint NumberUnaryNat _ = ⊤
  Number.fromNat NumberUnaryNat x = x
