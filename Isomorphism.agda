{-# OPTIONS --without-K --safe #-}

module Isomorphism where

open import Equality using (_≡_); open Equality._≡_
open import Functions using (id ; _∘_)

infixr 1 _≅_

record _≅_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    to-from : ∀ {b : B} → to (from b) ≡ b
    from-to : ∀ {a : A} → from (to a) ≡ a

≅-reflexive : ∀ {A : Set} → A ≅ A
≅-reflexive = record
  {
    to      = id   ;
    from    = id   ;
    to-from = refl ;
    from-to = refl
  }

≅-transitive : ∀ {A B C : Set} → A ≅ B → B ≅ C → A ≅ C
_≅_.to (≅-transitive i₁ i₂) = _≅_.to i₂ ∘ _≅_.to i₁
_≅_.from (≅-transitive i₁ i₂) = _≅_.from i₁ ∘ _≅_.from i₂
_≅_.to-from (≅-transitive i₁ i₂) {b} rewrite _≅_.to-from i₁ {_≅_.from i₂ b} = _≅_.to-from i₂
_≅_.from-to (≅-transitive i₁ i₂) {a} rewrite _≅_.from-to i₂ {_≅_.to i₁ a} = _≅_.from-to i₁

≅-symmetric : ∀ {A B : Set} → A ≅ B → B ≅ A
≅-symmetric i = record
  {
    to = _≅_.from i ;
    from = _≅_.to i ;
    to-from = _≅_.from-to i ;
    from-to = _≅_.to-from i
  }

infixr 0 _≅⟨_⟩_

_≅⟨_⟩_ : {B C : Set} → (A : Set) → A ≅ B → B ≅ C → A ≅ C
_ ≅⟨ i₁ ⟩ i₂ = ≅-transitive i₁ i₂

infixr 1 _∎

_∎ : (A : Set) → A ≅ A
_ ∎ = ≅-reflexive
