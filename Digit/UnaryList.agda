{-# OPTIONS --exact-split #-}

module Digit.UnaryList where

open import Agda.Builtin.Equality
open import Agda.Builtin.FromNat
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_*_ to _*Nat_; _+_ to _+Nat_)
open import Agda.Builtin.Unit
open import Container.List

data Digit : Set where
  𝟙 : Digit

increment : List Digit → List Digit
increment xs = 𝟙 ∷ xs

toNat : List Digit → Nat
toNat [] = zero
toNat (𝟙 ∷ xs) = suc (toNat xs)

instance
  NumberUnaryList : Number (List Digit)
  Number.Constraint NumberUnaryList _ = ⊤
  Number.fromNat NumberUnaryList zero = []
  Number.fromNat NumberUnaryList (suc n) = 𝟙 ∷ Number.fromNat NumberUnaryList n

fromℕ = Number.fromNat NumberUnaryList

test-zero : fromℕ(toNat 0) ≡ 0
test-zero = refl
test-one : fromℕ(toNat 1) ≡ 1
test-one = refl
test-two : fromℕ(toNat 2) ≡ 2
test-two = refl

right-identity : (n : Nat) → toNat(fromNat n) ≡ n
right-identity zero = refl
right-identity (suc n) rewrite right-identity n = refl

left-identity : (xs : List Digit) → fromNat(toNat xs) ≡ xs
left-identity [] = refl
left-identity (𝟙 ∷ xs) rewrite left-identity xs = refl
