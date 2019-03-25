{-# OPTIONS --without-K --safe #-}

module Product where

infixr 1 ⟨_,_⟩

record ∃ (X : Set) (Y : X → Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : X
    proj₂ : Y proj₁

infixr 1 _×_

_×_ : (X : Set) → (Y : Set) → Set
X × Y = ∃ X (λ _ → Y)
