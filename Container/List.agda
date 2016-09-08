{-# OPTIONS --exact-split #-}

module Container.List where

open import Agda.Builtin.List public
open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Basic.NumberNat

length
  : {la : Level}
  → {A : Set la}
  → List A
  → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

replicate
  : {la : Level}
  → {A : Set la}
  → (n : Nat)
  → A
  → List A
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

concat
  : {la : Level}
  → {A : Set la}
  → (xs ys : List A)
  → List A
concat [] ys = ys
concat (x ∷ xs) ys = x ∷ concat xs ys

concat-empty
  : {la : Level}
  → {A : Set la}
  → (xs : List A)
  → concat xs [] ≡ xs
concat-empty [] = refl
concat-empty (x ∷ xs) rewrite concat-empty xs = refl

append
  : {la : Level}
  → {A : Set la}
  → List A
  → A
  → List A
append [] x' = x' ∷ []
append (x ∷ xs) x' = x ∷ append xs x'

concat-append
  : {la : Level}
  → {A : Set la}
  → (xs : List A)
  → (x : A)
  → concat xs (x ∷ []) ≡ append xs x
concat-append [] x' = refl
concat-append (x ∷ xs) x' rewrite concat-append xs x' = refl

reverse-aux
  : {la : Level}
  → {A : Set la}
  → List A
  → List A
  → List A
reverse-aux rs [] = rs
reverse-aux rs (x ∷ xs) = reverse-aux (x ∷ rs) xs

reverse
  : {la : Level}
  → {A : Set la}
  → List A
  → List A
reverse = reverse-aux []
