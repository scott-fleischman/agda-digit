{-# OPTIONS --without-K #-}

module Digit.Fin3 where

module Equality where
  infix 4 _≡_
  data _≡_ {A : Set} (x : A) : A → Set where
    instance refl : x ≡ x
  {-# BUILTIN EQUALITY _≡_ #-}

  cong : {X Y : Set} -> (f : X -> Y) -> {x y : X} -> x ≡ y -> f x ≡ f y
  cong f refl = refl

module Natural where
  data Nat : Set where
    zero : Nat
    suc  : (n : Nat) → Nat

  {-# BUILTIN NATURAL Nat #-}

  record Number (A : Set) : Set1 where
    field
      Constraint : Nat → Set
      fromNat : (n : Nat) → {{_ : Constraint n}} → A

  open Number {{...}} public using (fromNat)

  {-# BUILTIN FROMNAT fromNat #-}
  {-# DISPLAY Number.fromNat _ n = fromNat n #-}
open Natural

data False : Set where
record True : Set where
  constructor <>

instance
  Number-Nat : Number Nat
  Number.Constraint Number-Nat _ = True
  Number.fromNat    Number-Nat n = n

data Bool : Set where
  true false : Bool

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

fin-to-nat : {n : Nat} -> Fin n -> Nat
fin-to-nat zero    = zero
fin-to-nat (suc f) = suc (fin-to-nat f)

_<Set_ : (n m : Nat) -> Set
zero <Set zero = False
zero <Set suc m = True
suc n <Set zero = False
suc n <Set suc m = n <Set m

nat-to-fin : (n : Nat) -> {m : Nat} -> {{p : n <Set m}} -> Fin m
nat-to-fin zero {zero} {{()}}
nat-to-fin zero {suc m} {{<>}} = zero
nat-to-fin (suc n) {zero} {{()}}
nat-to-fin (suc n) {suc m} = suc (nat-to-fin n)

instance
  Number-Fin : {n : Nat} → Number (Fin n)
  Number.Constraint (Number-Fin {n}) m = m <Set n
  Number.fromNat    Number-Fin       m = nat-to-fin m

data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0
  _,-_ : A -> {n : Nat} -> Vec A n -> Vec A (suc n)
infixr 6 _,-_

data Base+2 (base-2 : Nat) : Nat -> Set where
  zero : Base+2 base-2 0
  non-zero : {d : Nat} -> Fin (suc base-2) -> Vec (Fin (suc (suc base-2))) d -> Base+2 base-2 (suc d)

module Base+2-Examples where
  base2-0 : Base+2 0 0
  base2-0 = zero

  base2-1 : Base+2 0 1
  base2-1 = non-zero zero []

  base2-2 : Base+2 0 2
  base2-2 = non-zero zero (zero ,- [])

  base2-3 : Base+2 0 2
  base2-3 = non-zero zero (suc zero ,- [])

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

module FinAsIndex where
  direct-fin : Fin 5
  direct-fin = 4

  data FinIndex {n : Nat} : (Fin n) -> Set where
    fin-index : (f : Fin n) -> FinIndex f

  index-fin : FinIndex {5} 3
  index-fin = fin-index _

lift-fin-suc : {n : Nat} -> Fin n -> Fin (suc n)
lift-fin-suc {zero} ()
lift-fin-suc {suc n} zero = zero
lift-fin-suc {suc n} (suc f) = suc (lift-fin-suc f)

module LiftFinSuc-PreservesNumber where
  open Equality
  preserves-number : {n : Nat} -> (f : Fin n) -> fin-to-nat f ≡ fin-to-nat (lift-fin-suc f)
  preserves-number zero = refl
  preserves-number (suc f) = Equality.cong suc (preserves-number f)

_+F_ : {n : Nat} -> (x y : Fin (suc (suc n))) -> Fin 2 × Fin (suc (suc n))
zero +F y = zero , y
suc x +F zero = zero , suc x
_+F_ {zero} (suc x) (suc y) = suc zero , zero
_+F_ {suc n} (suc x) (suc y) with x +F y
_+F_ {suc n} (suc x) (suc y) | zero , z = zero , lift-fin-suc z
_+F_ {suc n} (suc x) (suc y) | suc c , z = {!!}

_+B_ : {b d : Nat} -> (x y : Base+2 b d) -> Fin 2 × Base+2 b d
zero +B y = zero , y
non-zero x xs +B non-zero y ys = {!!}
