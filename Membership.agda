{-# OPTIONS --without-K --safe #-}

module Membership where

open import Any using (AnyT); open Any.AnyT ⦃...⦄
open import Equality using (_≡_)

infixr 2 _∈_

_∈_ : {A : Set} {T : Set → Set} ⦃ _ : AnyT T ⦄ → A → T A → Set
a ∈ as = Any (_≡ a) as
