{-# OPTIONS --without-K --safe #-}

module Permutation (A : Set) where

open import Any using (AnyT); open Any.AnyT ⦃...⦄
open import Empty using (⊥ ; ⊥-elim)
open import Equality using (_≡_ ; _≡⟨_⟩_) renaming (_∎ to _∎-eq); open Equality._≡_
open import Fin using (Fin); open Fin.Fin
open import Functions using (_$_)
open import Isomorphism using (_≅_ ; _≅⟨_⟩_ ; _∎ ; ≅-reflexive ; ≅-symmetric ; ⊥-left-unit ; +-cong-left ; +-cong-right ; ∈-distr-++ ; +-assoc ; +-comm ; iso)
open import List using (List ; _++_ ; length ; lookup); open List.List
open import Membership using (_∈_)
open import Product using (∃ ; ⟨_,_⟩)
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

∃-cong : ∀ {as₁ as₂ : List A} → as₁ ≈ as₂ → ∃ A (λ a → a ∈ as₁) ≅ ∃ A (λ a → a ∈ as₂)
_≅_.to (∃-cong {as₁} {as₂} p) ⟨ a , x ⟩ = ⟨ a , _≅_.to p x ⟩
_≅_.from (∃-cong {as₁} {as₂} p) ⟨ a , x ⟩ = ⟨ a , _≅_.from p x ⟩
_≅_.to-from (∃-cong {as₁} {as₂} p) {⟨ a , x ⟩} rewrite _≅_.to-from p {x} = refl
_≅_.from-to (∃-cong {as₁} {as₂} p) {⟨ a , x ⟩} rewrite _≅_.from-to p {x} = refl

sound-iso : ∀ {as₁ as₂ : List A} → as₁ ≈ as₂ → Fin (length as₁) ≅ Fin (length as₂)
sound-iso {as₁} {as₂} p =
  Fin (length as₁)    ≅⟨ iso ⟩
  ∃ A (λ a → a ∈ as₁) ≅⟨ ∃-cong p ⟩
  ∃ A (λ a → a ∈ as₂) ≅⟨ ≅-symmetric iso ⟩
  Fin (length as₂)    ∎

lookup' : (as : List A) → ∃ A (λ a → a ∈ as) → A
lookup' [] ()
lookup' (_ :: _) ⟨ a , left _ ⟩ = a
lookup' (_ :: as) ⟨ a , right p ⟩ = lookup' as ⟨ a , p ⟩

lookup-eq : ∀ {as : List A} {i : Fin (length as)} → lookup as i ≡ lookup' as (_≅_.to iso i)
lookup-eq {[]} {()}
lookup-eq {a :: as} {fzero} = refl
lookup-eq {a :: as} {fsucc i} rewrite lookup-eq {as} {i} = refl

lookup-eq-2 : ∀ {as : List A} {e : ∃ A (λ a → a ∈ as)} → lookup' as e ≡ lookup as (_≅_.from iso e)
lookup-eq-2 {[]} {()}
lookup-eq-2 {_ :: _} {⟨ _ , left refl ⟩} = refl
lookup-eq-2 {_ :: as} {⟨ a , right x ⟩} rewrite lookup-eq-2 {as} {⟨ a , x ⟩} = refl

lemma : ∀ {a : A} {as : List A} {p : a ∈ as} → lookup' as ⟨ a , p ⟩ ≡ a
lemma {a} {[]} {()}
lemma {a} {a' :: as} {left refl} = refl
lemma {a} {a' :: as} {right x} = lemma {a} {as} {x}

lookup'-eq : ∀ {as₁ as₂ : List A} {e : ∃ A (λ a → a ∈ as₁)} → (p : as₁ ≈ as₂) → lookup' as₁ e ≡ lookup' as₂ (_≅_.to (∃-cong p) e)
lookup'-eq {as₁} {as₂} {⟨ a , x ⟩} p rewrite lemma {a} {as₁} {x} | lemma {a} {as₂} {_≅_.to p x} = refl

lookup-match : ∀ {as₁ as₂ : List A} {i : Fin (length as₁)} → (p : as₁ ≈ as₂) → lookup as₁ i ≡ lookup as₂ (_≅_.to (sound-iso p) i)
lookup-match {as₁} {as₂} {i} p =
  lookup as₁ i                                                 ≡⟨ lookup-eq {as₁} ⟩
  lookup' as₁ (_≅_.to iso i)                                   ≡⟨ lookup'-eq p ⟩
  lookup' as₂ (_≅_.to (∃-cong p) $ _≅_.to iso i)               ≡⟨ lookup-eq-2 {as₂}  ⟩
  lookup as₂ (_≅_.from iso $ _≅_.to (∃-cong p) $ _≅_.to iso i) ≡⟨ refl ⟩
  lookup as₂ (_≅_.to (sound-iso p) i)                          ∎-eq
