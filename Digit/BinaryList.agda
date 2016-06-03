{-# OPTIONS --exact-split #-}

module Digit.BinaryList where

open import Agda.Builtin.FromNat
open import Agda.Builtin.Nat using (Nat) renaming (zero to Z; suc to S; _*_ to _*Nat_; _+_ to _+Nat_)
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Container.List
open import Container.Product
open import Digit.Binary
open import Digit.UnaryNat

infixl 6 _+_
infixl 7 _*_

increment : List Digit → List Digit
increment [] = 𝟙 ∷ []
increment (𝟘 ∷ xs) = 𝟙 ∷ xs
increment (𝟙 ∷ xs) = 𝟘 ∷ increment (xs)

toNat : List Digit → Nat
toNat [] = 0
toNat (𝟘 ∷ xs) = 2 *Nat (toNat xs)
toNat (𝟙 ∷ xs) = S (2 *Nat (toNat xs))

instance
  NumberBinaryList : Number (List Digit)
  Number.Constraint NumberBinaryList _ = ⊤
  Number.fromNat NumberBinaryList Z = []
  Number.fromNat NumberBinaryList (S n) = increment (Number.fromNat NumberBinaryList n)

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
normalize (𝟘 ∷ _) | [] = []
normalize (𝟙 ∷ _) | [] = 𝟙 ∷ []
normalize (x ∷ _) | x' ∷ xs' = x ∷ x' ∷ xs'

normalize-idempotent : (xs : List Digit) → normalize (normalize xs) ≡ normalize xs
normalize-idempotent [] = refl
normalize-idempotent (x ∷ xs) with normalize xs | normalize-idempotent xs
normalize-idempotent (𝟘 ∷ xs) | [] | refl = refl
normalize-idempotent (𝟙 ∷ xs) | [] | refl = refl
normalize-idempotent (x ∷ xs) | x' ∷ xs' | p rewrite p = refl

normalize-append-zero
  : (xs : List Digit)
  → normalize (append xs 𝟘) ≡ normalize xs
normalize-append-zero [] = refl
normalize-append-zero (x ∷ xs) with normalize xs | normalize-append-zero xs
normalize-append-zero (𝟘 ∷ xs) | [] | p rewrite p = refl
normalize-append-zero (𝟙 ∷ xs) | [] | p rewrite p = refl
normalize-append-zero (x ∷ xs) | x' ∷ xs' | p rewrite p = refl

normalize-add-two-zeros
  : (xs : List Digit)
  → normalize (append (append xs 𝟘) 𝟘) ≡ normalize xs
normalize-add-two-zeros xs rewrite normalize-append-zero (append xs 𝟘) | normalize-append-zero xs = refl

normalize-replicate
  : (xs : List Digit)
  → (n : Nat)
  → normalize (concat xs (replicate n 𝟘)) ≡ normalize xs
normalize-replicate xs Z rewrite concat-empty xs = refl
normalize-replicate [] (S n) rewrite normalize-replicate [] n = refl
normalize-replicate (x ∷ xs) (S n) with xs | normalize xs | normalize-replicate xs (S n)
normalize-replicate (𝟘 ∷ xs) (S n) | xs' | [] | p rewrite p = refl
normalize-replicate (𝟙 ∷ xs) (S n) | xs' | [] | p rewrite p = refl
normalize-replicate (x ∷ xs) (S n) | xs' | nx ∷ nxs | p rewrite p = refl
