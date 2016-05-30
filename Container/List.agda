{-# OPTIONS --exact-split #-}

module Container.List where

open import Agda.Builtin.List public

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

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
