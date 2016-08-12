module Digit.Fin where

open import Agda.Builtin.Nat
  using (Nat; zero; suc)
  renaming (_+_ to _+ℕ_)
  renaming (_*_ to _*ℕ_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Container.List using (length)
open import Container.Vector

data Fin : Nat → Set where
  zero : {n : Nat} → Fin n
  suc : {n : Nat} → Fin n → Fin (suc n)

infixl 8 _^ℕ_
_^ℕ_ : (x y : Nat) → Nat
x ^ℕ zero = 1
x ^ℕ suc y = x *ℕ (x ^ℕ y)

module Test^ where
  5^0 : 5 ^ℕ 0 ≡ 1
  5^0 = refl

  2^3 : 2 ^ℕ 3 ≡ 8
  2^3 = refl

fin-toℕ : {n : Nat} → Fin n → Nat
fin-toℕ zero = 0
fin-toℕ (suc x) = suc (fin-toℕ x)

toℕ : {d : Nat} → List (Fin d) → Nat
toℕ [] = 0
toℕ {d} (x ∷ xs) = (fin-toℕ x) *ℕ (d ^ℕ length xs) +ℕ toℕ xs

vec-toℕ : {n d : Nat} → Vec (Fin d) n → Nat
vec-toℕ [] = 0
vec-toℕ {n = suc n} {d} (x ∷ xs) = (fin-toℕ x) *ℕ (d ^ℕ n) +ℕ vec-toℕ xs

module TestDigit where
  b2-0 : List (Fin 2)
  b2-0 = []

  b2-0≡0 : toℕ b2-0 ≡ 0
  b2-0≡0 = refl

  b101 : Vec (Fin 2) _
  b101 = (suc zero) ∷ zero ∷ (suc zero) ∷ []

  b101≡5 : vec-toℕ b101 ≡ 5
  b101≡5 = refl

  b3-120 : List (Fin 3)
  b3-120 = (suc zero) ∷ (suc (suc zero)) ∷ zero ∷ []

  b3-120≡15 : toℕ b3-120 ≡ 15
  b3-120≡15 = refl
