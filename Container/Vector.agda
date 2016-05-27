{-# OPTIONS --exact-split #-}

module Container.Vector where

open import Agda.Primitive
open import Agda.Builtin.Nat

data Vec {la : Level} (A : Set la) : Nat → Set la where
  end : Vec A zero
  add : {n : Nat} → A → Vec A n → Vec A (suc n)

map
  : {la lb : Level}
  → {A : Set la}
  → {B : Set lb}
  → {n : Nat}
  → (A → B)
  → Vec A n
  → Vec B n
map f end = end
map f (add x xs) = add (f x) (map f xs)

pure
  : {la : Level}
  → {A : Set la}
  → A
  → Vec A 1
pure x = add x end

apply
  : {la lb : Level}
  → {A : Set la}
  → {B : Set lb}
  → {n : Nat}
  → Vec (A → B) n
  → Vec A n
  → Vec B n
apply end end = end
apply (add f fs) (add x xs) = add (f x) (apply fs xs)

append
  : {la : Level}
  → {A : Set la}
  → {n m : Nat}
  → Vec A n
  → Vec A m
  → Vec A (n + m)
append end ys = ys
append (add x xs) ys = add x (append xs ys)
