{-# OPTIONS --without-K --safe #-}

module Permutation where

open import Any using (AnyT); open Any.AnyT ⦃...⦄
open import Isomorphism using (_≅_)
open import Membership using (_∈_)

infixr 2 _≈_

_≈_ : {T₁ T₂ : Set → Set} ⦃ _ : AnyT T₁ ⦄ ⦃ _ : AnyT T₂ ⦄ {A : Set} → T₁ A → T₂ A → Set
as₁ ≈ as₂ = ∀ {a} → a ∈ as₁ ≅ a ∈ as₂
