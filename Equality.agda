{-# OPTIONS --without-K --safe #-}

module Equality where

open import Empty using (⊥)

infixr 4 _≡_

data _≡_ {A : Set} (a : A)  : A → Set where
  refl : a ≡ a

_≢_ : {A : Set} → A → A → Set
a₁ ≢ a₂ = a₁ ≡ a₂ → ⊥

≡-symmetric : ∀ {A : Set} {a₁ a₂ : A} → a₁ ≡ a₂ → a₂ ≡ a₁
≡-symmetric refl = refl

≡-transitive : ∀ {A : Set} {a₁ a₂ a₃ : A} → a₁ ≡ a₂ → a₂ ≡ a₃ → a₁ ≡ a₃
≡-transitive refl refl = refl

{-# BUILTIN EQUALITY _≡_ #-}

infixr 0 _≡⟨_⟩_

_≡⟨_⟩_ : {A : Set} → (a₁ : A) → {a₂ a₃ : A} → (a₁ ≡ a₂) → (a₂ ≡ a₃) → a₁ ≡ a₃
_ ≡⟨ e₁ ⟩ e₂ = ≡-transitive e₁ e₂

infixr 1 _∎

_∎ : {A : Set} → (a : A) → a ≡ a
a ∎ = refl
