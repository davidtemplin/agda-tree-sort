{-# OPTIONS --without-K --safe #-}

module List where

open import Any using (AnyT); open Any.AnyT ⦃...⦄
open import Empty using (⊥)
open import Fin using (Fin); open Fin.Fin
open import Nat using (ℕ); open Nat.ℕ
open import Sum using (_+_)

infixr 3 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

infixr 1 _++_

_++_ : {A : Set} → List A → List A → List A
[]         ++ as₂ = as₂
(a :: as₁) ++ as₂ = a :: (as₁ ++ as₂)

length : {A : Set} → List A → ℕ
length [] = zero
length (a :: as) = succ (length as)

lookup : {A : Set} → (as : List A) → Fin (length as) → A
lookup [] ()
lookup (a :: _) fzero = a
lookup (_ :: as) (fsucc i) = lookup as i

instance
  AnyList : AnyT List
  Any ⦃ AnyList ⦄ = AnyListImpl
    where
      AnyListImpl : {A : Set} → (A → Set) → List A → Set
      AnyListImpl P []        = ⊥
      AnyListImpl P (a :: as) = P a + AnyListImpl P as
