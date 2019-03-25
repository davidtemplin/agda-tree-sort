{-# OPTIONS --without-K --safe #-}

module Implication where

open import Functions using (id ; _∘_)

infixr 0 _→⟨_⟩_

_→⟨_⟩_ : {B C : Set} → (A : Set) → (A → B) → (B → C) → (A → C)
_ →⟨ p₁ ⟩ p₂ = p₂ ∘ p₁

infixr 1 _∎

_∎ : (A : Set) → (A → A)
_∎ _ = id

infixr 0 _↔_

record _↔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
