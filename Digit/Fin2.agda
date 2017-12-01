module Digit.Fin2 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat hiding (_-_)
open import Agda.Builtin.FromNat

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

_<=Set_ : (n m : Nat) -> Set
zero <=Set m = True
suc n <=Set zero = False
suc n <=Set suc m = n <=Set m

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

record VecR (A : Set) : Set where
  constructor vecr
  field
    {length} : Nat
    items : Vec A length

set-value-at-index : {A : Set} -> {n : Nat} -> Vec A n -> Fin n -> A -> Vec A n
set-value-at-index (v ,- vs) zero    v' = v' ,- vs
set-value-at-index (v ,- vs) (suc i) v' = v  ,- set-value-at-index vs i v'

-- here, `Vec Bool n` represents a set of (unique) values of `Fin n`
insert-value : {n : Nat} -> Vec Bool n -> Fin n -> Vec Bool n
insert-value bs f = set-value-at-index bs f true

data IncFinResult (n : Nat) : Set where
  carry : IncFinResult n
  non-carry : Fin n -> IncFinResult n

inc-fin : {n : Nat} -> Fin n -> IncFinResult n
inc-fin {suc zero} zero = carry
inc-fin {suc zero} (suc ())
inc-fin {suc (suc n)} zero = non-carry (suc zero)
inc-fin {suc (suc n)} (suc f) with inc-fin f
inc-fin {suc (suc n)} (suc f) | carry = carry
inc-fin {suc (suc n)} (suc f) | non-carry f' = non-carry (suc f')

module test-inc-fin where
  unary0 : inc-fin {1} 0 ≡ carry
  unary0 = refl

  0-base-5 : inc-fin {5} 0 ≡ non-carry 1
  0-base-5 = refl

  3-base-5 : inc-fin {5} 3 ≡ non-carry 4
  3-base-5 = refl

  4-base-5 : inc-fin {5} 4 ≡ carry
  4-base-5 = refl

inc-vecr-digit : {d : Nat} -> VecR (Fin (suc d)) -> VecR (Fin (suc d))
inc-vecr-digit {zero}  (vecr []) = vecr (0 ,- [])
inc-vecr-digit {suc d} (vecr []) = vecr (1 ,- [])

{-# CATCHALL #-}
inc-vecr-digit (vecr (x ,- items)) with inc-fin x
inc-vecr-digit (vecr (x ,- items)) | carry with inc-vecr-digit (vecr items)
inc-vecr-digit (vecr (x ,- items)) | carry | vecr items' = vecr (0 ,- items')
inc-vecr-digit (vecr (x ,- items)) | non-carry x' = vecr (x' ,- items)

module test-inc-vecr-digit where
  unary0 : inc-vecr-digit {0} (vecr []) ≡ vecr (0 ,- [])
  unary0 = refl

  unary1 : inc-vecr-digit {0} (vecr (0 ,- [])) ≡ vecr (0 ,- 0 ,- [])
  unary1 = refl

  unary2 : inc-vecr-digit {0} (vecr (0 ,- 0 ,- [])) ≡ vecr (0 ,- 0 ,- 0 ,- [])
  unary2 = refl

  3-base-5 : inc-vecr-digit {4} (vecr (3 ,- [])) ≡ vecr (4 ,- [])
  3-base-5 = refl

  4-base-5 : inc-vecr-digit {4} (vecr (4 ,- [])) ≡ vecr (0 ,- 1 ,- [])
  4-base-5 = refl

  99-decimal : inc-vecr-digit {9} (vecr (9 ,- 9 ,- [])) ≡ vecr (0 ,- 0 ,- 1 ,- [])
  99-decimal = refl

nat-to-vecr-digit : {d : Nat} -> (n : Nat) -> VecR (Fin (suc d))
nat-to-vecr-digit zero = vecr []
nat-to-vecr-digit (suc n) = inc-vecr-digit (nat-to-vecr-digit n)

vecr-digit-to-nat : {d : Nat} -> VecR (Fin (suc d)) -> Nat
vecr-digit-to-nat (vecr []) = 0
vecr-digit-to-nat {d} (vecr (x ,- items)) = fin-to-nat x + (suc d) * vecr-digit-to-nat (vecr items)

round-trip-base : (d : Nat) -> Nat -> Nat
round-trip-base d n = vecr-digit-to-nat (nat-to-vecr-digit {d} n)
