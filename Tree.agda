{-# OPTIONS --without-K --safe #-}

module Tree where

open import Any using (AnyT); open Any.AnyT ⦃...⦄
open import Empty using (⊥)
open import Sum using (_+_)

data Tree (A : Set) : Set where
  empty : Tree A
  node  : Tree A → A → Tree A → Tree A

AnyTreeImpl : {A : Set} → (A → Set) → Tree A → Set
AnyTreeImpl P empty        = ⊥
AnyTreeImpl P (node l a r) = AnyTreeImpl P l + P a + AnyTreeImpl P r

instance
  AnyTree : AnyT Tree
  Any ⦃ AnyTree ⦄ = AnyTreeImpl
