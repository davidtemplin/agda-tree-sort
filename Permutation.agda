{-# OPTIONS --without-K --safe #-}

module Permutation (A : Set) where

open import Any using (AnyT); open Any.AnyT ⦃...⦄
open import Empty using (⊥ ; ⊥-elim)
open import Equality using (_≡_); open Equality._≡_
open import Functions using (_$_)
open import Isomorphism using (_≅_ ; _≅⟨_⟩_ ; _∎ ; ≅-reflexive ; ≅-symmetric ; ⊥-left-unit ; +-cong-left ; +-cong-right ; ∈-distr-++ ; +-assoc ; +-comm)
open import List using (List ; _++_); open List.List
open import Membership using (_∈_)
open import Sum using (_+_); open Sum._+_
open import Tree using (Tree); open Tree.Tree

infixr 2 _≈_

_≈_ : {T₁ T₂ : Set → Set} ⦃ _ : AnyT T₁ ⦄ ⦃ _ : AnyT T₂ ⦄ → T₁ A → T₂ A → Set
as₁ ≈ as₂ = ∀ {a} → a ∈ as₁ ≅ a ∈ as₂

empty≈[] : ∀ {a : A} → a ∈ empty ≅ a ∈ []
_≅_.to empty≈[] ()
_≅_.from empty≈[] ()
_≅_.to-from empty≈[] {()}
_≅_.from-to empty≈[] {()}

empty-lemma : {as : List A} → as ≈ empty → as ≡ []
empty-lemma {[]} _ = refl
empty-lemma {_ :: _} p = ⊥-elim $ _≅_.to p $ left refl

singleton-lemma : {a : A} → a :: [] ≈ node empty a empty
singleton-lemma {a} {x} =
  x ∈ a :: []            ≅⟨ ≅-reflexive ⟩
  a ≡ x + ⊥              ≅⟨ ⊥-left-unit ⟩
  ⊥ + a ≡ x + ⊥          ≅⟨ ≅-reflexive ⟩
  x ∈ node empty a empty ∎

::-cong : ∀ {a : A} {as₁ as₂ : List A} → as₁ ≈ as₂ → a :: as₁ ≈ a :: as₂
::-cong {a} {as₁} {as₂} p {x} =
  x ∈ a :: as₁    ≅⟨ ≅-reflexive ⟩
  a ≡ x + x ∈ as₁ ≅⟨ +-cong-right p ⟩
  a ≡ x + x ∈ as₂ ≅⟨ ≅-reflexive ⟩
  x ∈ a :: as₂    ∎

[]-lemma : ∀ {as : List A} → as ≈ [] → as ≡ []
[]-lemma {[]} p = refl
[]-lemma {a :: as} p = ⊥-elim $ _≅_.to p $ left refl

++-cong-left : ∀ {as₁ as₂ as₁' : List A} → as₁ ≈ as₁' → (as₁ ++ as₂) ≈ (as₁' ++ as₂)
++-cong-left {as₁} {as₂} {as₁'} p {x} =
  x ∈ (as₁ ++ as₂)   ≅⟨ ∈-distr-++ ⟩
  x ∈ as₁ + x ∈ as₂  ≅⟨ +-cong-left p ⟩
  x ∈ as₁' + x ∈ as₂ ≅⟨ ≅-symmetric ∈-distr-++ ⟩
  x ∈ (as₁' ++ as₂)  ∎

++-cong-right : ∀ {as₁ as₂ as₂' : List A} → as₂ ≈ as₂' → (as₁ ++ as₂) ≈ (as₁ ++ as₂')
++-cong-right {as₁} {as₂} {as₂'} p {x} =
  x ∈ (as₁ ++ as₂)   ≅⟨ ∈-distr-++ ⟩
  x ∈ as₁ + x ∈ as₂  ≅⟨ +-cong-right p ⟩
  x ∈ as₁ + x ∈ as₂' ≅⟨ ≅-symmetric ∈-distr-++ ⟩
  x ∈ (as₁ ++ as₂')  ∎

shift-lemma : ∀ {a : A} {as₁ as₂ : List A} → (a :: (as₁ ++ as₂)) ≈ (as₁ ++ a :: as₂)
shift-lemma {a} {as₁} {as₂} {x} =
  x ∈ a :: (as₁ ++ as₂)       ≅⟨ ≅-reflexive ⟩
  a ≡ x + x ∈ (as₁ ++ as₂)    ≅⟨ +-cong-right ∈-distr-++ ⟩
  a ≡ x + x ∈ as₁ + x ∈ as₂   ≅⟨ +-assoc  ⟩
  (a ≡ x + x ∈ as₁) + x ∈ as₂ ≅⟨ +-cong-left +-comm ⟩
  (x ∈ as₁ + a ≡ x) + x ∈ as₂ ≅⟨ ≅-symmetric +-assoc ⟩
  x ∈ as₁ + a ≡ x + x ∈ as₂   ≅⟨ ≅-reflexive ⟩
  x ∈ as₁ + x ∈ a :: as₂      ≅⟨ ≅-symmetric ∈-distr-++ ⟩
  x ∈ (as₁ ++ a :: as₂)       ∎

swap-lemma : ∀ {a₁ a₂ : A} {as : List A} → a₁ :: a₂ :: as ≈ a₂ :: a₁ :: as
swap-lemma {a₁} {a₂} {as} {x} =
  x ∈ a₁ :: a₂ :: as         ≅⟨ ≅-reflexive ⟩
  a₁ ≡ x + (a₂ ≡ x + x ∈ as) ≅⟨ +-assoc ⟩
  (a₁ ≡ x + a₂ ≡ x) + x ∈ as ≅⟨ +-cong-left +-comm ⟩
  (a₂ ≡ x + a₁ ≡ x) + x ∈ as ≅⟨ ≅-symmetric +-assoc ⟩
  a₂ ≡ x + a₁ ≡ x + x ∈ as   ≅⟨ ≅-reflexive ⟩
  x ∈ a₂ :: a₁ :: as         ∎
