{-# OPTIONS --exact-split #-}

module Container.Product where

open import Agda.Primitive

data Product {la lb : Level} (A : Set la) (B : Set lb) : Set (la ⊔ lb) where
  product : A → B → Product A B

_×_ = Product

_,_ : {la lb : Level} {A : Set la} {B : Set lb} → A → B → A × B
_,_ = product
