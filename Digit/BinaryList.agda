{-# OPTIONS --exact-split #-}

module Digit.BinaryList where

open import Agda.Builtin.Nat using (Nat) renaming (zero to Z; suc to S; _*_ to _*Nat_; _+_ to _+Nat_)
open import Agda.Builtin.Equality
open import Container.List
open import Container.Product

infixl 6 _+_
infixl 7 _*_

data Digit : Set where
  𝟘 𝟙 : Digit

increment : List Digit → List Digit
increment [] = 𝟙 ∷ []
increment (𝟘 ∷ xs) = 𝟙 ∷ xs
increment (𝟙 ∷ xs) = 𝟘 ∷ increment (xs)

toNat : List Digit → Nat
toNat [] = 0
toNat (𝟘 ∷ xs) = 2 *Nat (toNat xs)
toNat (𝟙 ∷ xs) = S (2 *Nat (toNat xs))

fromNat : Nat → List Digit
fromNat 0 = []
fromNat (S n) = increment (fromNat n)

{-# BUILTIN FROMNAT fromNat #-}

_+_ : List Digit → List Digit → List Digit
[] + y = y
(x ∷ xs) + [] = (x ∷ xs)
(𝟘 ∷ xs) + (𝟘 ∷ ys) = 𝟘 ∷ xs + ys
(𝟘 ∷ xs) + (𝟙 ∷ ys) = 𝟙 ∷ xs + ys
(𝟙 ∷ xs) + (𝟘 ∷ ys) = 𝟙 ∷ xs + ys
(𝟙 ∷ xs) + (𝟙 ∷ ys) = 𝟘 ∷ increment (xs + ys)

shift-right : List Digit → List Digit
shift-right xs = 𝟘 ∷ xs

_*_ : List Digit → List Digit → List Digit
[] * y = []
(𝟘 ∷ xs) * ys = xs * shift-right ys
(𝟙 ∷ xs) * ys = ys + (xs * shift-right ys)

normalize : List Digit → List Digit
normalize [] = []
normalize (x ∷ xs) with normalize xs
normalize (𝟘 ∷ xs) | [] = []
normalize (𝟙 ∷ xs) | [] = 𝟙 ∷ []
normalize (x ∷ xs) | x' ∷ xs' = x ∷ x' ∷ xs'

normalize0-1 : normalize (𝟘 ∷ []) ≡ []
normalize0-1 = refl
normalize0-2 : normalize (𝟘 ∷ 𝟘 ∷ []) ≡ []
normalize0-2 = refl
normalize0-3 : normalize (𝟘 ∷ 𝟘 ∷ 𝟘 ∷ []) ≡ []
normalize0-3 = refl
normalize1-1 : normalize (𝟙 ∷ 𝟘 ∷ []) ≡ (𝟙 ∷ [])
normalize1-1 = refl
normalize1-2 : normalize (𝟙 ∷ 𝟘 ∷ 𝟘 ∷ []) ≡ (𝟙 ∷ [])
normalize1-2 = refl

normalize-idempotent : (xs : List Digit) → normalize (normalize xs) ≡ normalize xs
normalize-idempotent [] = refl
normalize-idempotent (x ∷ xs) with normalize xs | normalize-idempotent xs
normalize-idempotent (𝟘 ∷ xs) | [] | refl = refl
normalize-idempotent (𝟙 ∷ xs) | [] | refl = refl
normalize-idempotent (x ∷ xs) | x' ∷ xs' | p rewrite p = refl

normalize-empty-replicate : (n : Nat) → normalize (concat [] (replicate n 𝟘)) ≡ []
normalize-empty-replicate Z = refl
normalize-empty-replicate (S n) rewrite normalize-empty-replicate n = refl

normalize-zero-replicate : (n : Nat) → normalize (concat (normalize (𝟘 ∷ [])) (replicate n 𝟘)) ≡ []
normalize-zero-replicate Z = refl
normalize-zero-replicate (S n) rewrite normalize-zero-replicate n = refl

normalize-spec
  : (xs : List Digit)
  → (n : Nat)
  → normalize
      (concat
        (normalize xs)
        (replicate n 𝟘))
    ≡ normalize xs
normalize-spec xs Z rewrite concat-empty (normalize xs) | normalize-idempotent xs = refl
normalize-spec [] (S n) rewrite normalize-empty-replicate n = refl
normalize-spec (x ∷ xs) (S n) with normalize xs | normalize-spec xs (S n)
normalize-spec (𝟘 ∷ xs) (S n) | [] | p rewrite normalize-zero-replicate n = refl
normalize-spec (𝟙 ∷ xs) (S n) | [] | p rewrite normalize-zero-replicate n = refl
normalize-spec (x ∷ xs) (S n) | x' ∷ nxs | p rewrite p = refl
