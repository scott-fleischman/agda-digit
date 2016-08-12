{-# OPTIONS --exact-split #-}

module Container.Vector where

open import Agda.Primitive
open import Agda.Builtin.Nat

infixr 5 _∷_
infixl 4 _⊛_
data Vec {la : Level} (A : Set la) : Nat → Set la where
  [] : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

map
  : {la lb : Level}
  → {A : Set la}
  → {B : Set lb}
  → {n : Nat}
  → (A → B)
  → Vec A n
  → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

pure
  : {la : Level}
  → {A : Set la}
  → A
  → Vec A 1
pure x = x ∷ []

apply
  : {la lb : Level}
  → {A : Set la}
  → {B : Set lb}
  → {n : Nat}
  → Vec (A → B) n
  → Vec A n
  → Vec B n
apply [] [] = []
apply (f ∷ fs) (x ∷ xs) = f x ∷ apply fs xs

_⊛_ = apply

concat
  : {la : Level}
  → {A : Set la}
  → {n m : Nat}
  → Vec A n
  → Vec A m
  → Vec A (n + m)
concat [] ys = ys
concat (x ∷ xs) ys = x ∷ concat xs ys

replicate
  : {la : Level}
  → {A : Set la}
  → (n : Nat)
  → A
  → Vec A n
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

foldr
  : {la lb : Level}
  → {A : Set la}
  → {B : Set lb}
  → {n : Nat}
  → (A → B → B)
  → Vec A n
  → B
  → B
foldr f [] b = b
foldr f (x ∷ xs) b = f x (foldr f xs b)

import Container.List as List
toList
  : {la : Level}
  → {A : Set la}
  → {n : Nat}
  → Vec A n
  → List.List A
toList [] = List.[]
toList (x ∷ xs) = x List.∷ toList xs

record VecR {la : Level} (A : Set la) : Set la where
  constructor vector
  field
    length : Nat
    items : Vec A length

toVec
  : {la : Level}
  → {A : Set la}
  → List.List A
  → VecR A
toVec List.[] = vector zero []
toVec (x List.∷ xs) with toVec xs
toVec (x List.∷ xs) | vector length items = vector (suc length) (x ∷ items)
