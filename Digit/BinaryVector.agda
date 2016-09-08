{-# OPTIONS --exact-split #-}

module Digit.BinaryVector where

open import Agda.Builtin.Nat using (Nat)
open import Basic.NumberNat
open import Container.Product
open import Container.Vector
open import Digit.Binary

data Carry : Set where
  C0 C1 : Carry

increment : {n : Nat} → Vec Digit n → Vec Digit n × Carry
increment [] = [] , C1
increment (𝟘 ∷ xs) = 𝟙 ∷ xs , C0
increment (𝟙 ∷ xs) with increment xs
increment (𝟙 ∷ xs) | product xs' c = 𝟘 ∷ xs' , c

_+D_ : Digit → Digit → Digit × Carry
𝟘 +D y = y , C0
𝟙 +D 𝟘 = 𝟙 , C0
𝟙 +D 𝟙 = 𝟙 , C1

add-carry-digit : Carry → Digit → Digit → Digit × Carry
add-carry-digit C0 𝟘 y = y , C0
add-carry-digit C0 𝟙 𝟘 = 𝟙 , C0
add-carry-digit C0 𝟙 𝟙 = 𝟘 , C1
add-carry-digit C1 𝟘 𝟘 = 𝟙 , C0
add-carry-digit C1 𝟘 𝟙 = 𝟘 , C1
add-carry-digit C1 𝟙 𝟘 = 𝟘 , C1
add-carry-digit C1 𝟙 𝟙 = 𝟙 , C1

add-carry : {n : Nat} → Carry → Vec Digit n → Vec Digit n → Vec Digit n × Carry
add-carry c [] [] = [] , c
add-carry c (x ∷ xs) (y ∷ ys) with add-carry-digit c x y
add-carry c (x ∷ xs) (y ∷ ys) | product d c′ with add-carry c′ xs ys
add-carry c (x ∷ xs) (y ∷ ys) | product d c′ | product ds c″ = d ∷ ds , c″

_+_ : {n : Nat} → Vec Digit n → Vec Digit n → Vec Digit n × Carry
_+_ = add-carry C0

uint8 = Vec Digit 8
uint16 = Vec Digit 16
uint32 = Vec Digit 32

open import Agda.Builtin.Char
open import Agda.Builtin.String

toChar : Digit → Char
toChar 𝟘 = '0'
toChar 𝟙 = '1'

toString : {n : Nat} → Vec Digit n → String
toString xs = primStringFromList (toList (map toChar xs))
