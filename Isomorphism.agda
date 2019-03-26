{-# OPTIONS --without-K --safe #-}

module Isomorphism where

open import Empty using (⊥)
open import Equality using (_≡_); open Equality._≡_
open import Fin using (Fin); open Fin.Fin
open import Functions using (id ; _∘_ ; _$_)
open import List using (List ; _++_ ; length); open List.List
open import Membership using (_∈_)
open import Product using (∃ ; ⟨_,_⟩); open Product.∃
open import Sum using (_+_); open Sum._+_

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

+-cong-left : ∀ {X X' Y : Set} → X ≅ X' → (X + Y) ≅ (X' + Y)
_≅_.to (+-cong-left i) (left x) = left $ _≅_.to i x
_≅_.to (+-cong-left i) (right x) = right x
_≅_.from (+-cong-left i) (left x) = left $ _≅_.from i x
_≅_.from (+-cong-left i) (right y) = right y
_≅_.to-from (+-cong-left i) {left x} rewrite _≅_.to-from i {x} = refl
_≅_.to-from (+-cong-left i) {right x} = refl
_≅_.from-to (+-cong-left i) {left x} rewrite _≅_.from-to i {x} = refl
_≅_.from-to (+-cong-left i) {right x} = refl

+-cong-right : ∀ {X Y Y' : Set} → Y ≅ Y' → (X + Y) ≅ (X + Y')
_≅_.to (+-cong-right i) (left x) = left x
_≅_.to (+-cong-right i) (right x) = right $ _≅_.to i x
_≅_.from (+-cong-right i) (left x) = left x
_≅_.from (+-cong-right i) (right x) = right $ _≅_.from i x
_≅_.to-from (+-cong-right i) {left x} = refl
_≅_.to-from (+-cong-right i) {right x} rewrite _≅_.to-from i {x} = refl
_≅_.from-to (+-cong-right i) {left x} = refl
_≅_.from-to (+-cong-right i) {right x} rewrite _≅_.from-to i {x} = refl

+-cong : ∀ {X X' Y Y' : Set} → X ≅ X' → Y ≅ Y' → (X + Y) ≅ (X' + Y')
+-cong i₁ i₂ = ≅-transitive (+-cong-left i₁) (+-cong-right i₂)

+-comm : ∀ {X Y : Set} → (X + Y) ≅ (Y + X)
_≅_.to +-comm (left x) = right x
_≅_.to +-comm (right x) = left x
_≅_.from +-comm (left x) = right x
_≅_.from +-comm (right x) = left x
_≅_.to-from +-comm {left x} = refl
_≅_.to-from +-comm {right x} = refl
_≅_.from-to +-comm {left x} = refl
_≅_.from-to +-comm {right x} = refl

+-assoc : ∀ {X Y Z : Set} → (X + (Y + Z)) ≅ ((X + Y) + Z)
_≅_.to +-assoc (left x) = left (left x)
_≅_.to +-assoc (right (left y)) = left (right y)
_≅_.to +-assoc (right (right z)) = right z
_≅_.from +-assoc (left (left x)) = left x
_≅_.from +-assoc (left (right y)) = right (left y)
_≅_.from +-assoc (right z) = right (right z)
_≅_.to-from +-assoc {left (left x)} = refl
_≅_.to-from +-assoc {left (right y)} = refl
_≅_.to-from +-assoc {right z} = refl
_≅_.from-to +-assoc {left x} = refl
_≅_.from-to +-assoc {right (left y)} = refl
_≅_.from-to +-assoc {right (right z)} = refl

⊥-left-unit : ∀ {X : Set} → X ≅ ⊥ + X
_≅_.to ⊥-left-unit = right
_≅_.from ⊥-left-unit (left ())
_≅_.from ⊥-left-unit (right x) = x
_≅_.to-from ⊥-left-unit {left ()}
_≅_.to-from ⊥-left-unit {right x} = refl
_≅_.from-to ⊥-left-unit {x} = refl

∈-distr-++ : ∀ {A : Set} {x : A} {as₁ as₂ : List A} → (x ∈ (as₁ ++ as₂)) ≅ (x ∈ as₁ + x ∈ as₂)
∈-distr-++ {A} {x} {[]} {as₂} =
  x ∈ ([] ++ as₂)    ≅⟨ ≅-reflexive ⟩
  x ∈ as₂            ≅⟨ ⊥-left-unit ⟩
  ⊥ + x ∈ as₂        ≅⟨ ≅-reflexive ⟩
  (x ∈ [] + x ∈ as₂) ∎
∈-distr-++ {A} {x} {a :: as₁} {as₂} =
  x ∈ (a :: as₁ ++ as₂)         ≅⟨ ≅-reflexive ⟩
  a ≡ x + x ∈ (as₁ ++ as₂)      ≅⟨ +-cong-right ∈-distr-++ ⟩
  a ≡ x + x ∈ as₁ + x ∈ as₂     ≅⟨ +-assoc  ⟩
  (a ≡ x + x ∈ as₁) + x ∈ as₂   ≅⟨ ≅-reflexive ⟩
  (x ∈ (a :: as₁) + x ∈ as₂)    ∎

iso : ∀ {A : Set} {as : List A} → Fin (length as) ≅ ∃ A (λ a → a ∈ as)
_≅_.to (iso {A} {[]}) ()
_≅_.to (iso {A} {a :: _}) fzero = ⟨ a , left refl ⟩
_≅_.to (iso {A} {_ :: _}) (fsucc i) = let r = _≅_.to iso i in ⟨ proj₁ r , right (proj₂ r) ⟩
_≅_.from (iso {A} {[]}) ()
_≅_.from (iso {A} {_ :: _}) ⟨ _ , left _ ⟩ = fzero
_≅_.from (iso {A} {_ :: _}) ⟨ a' , right x ⟩ = fsucc (_≅_.from iso ⟨ a' , x ⟩)
_≅_.to-from (iso {A} {[]}) {()}
_≅_.to-from (iso {A} {_ :: _}) {⟨ _ , left refl ⟩} = refl
_≅_.to-from (iso {A} {_ :: _}) {⟨ a' , right x ⟩} rewrite (_≅_.to-from iso) {⟨ a' , x ⟩} = refl
_≅_.from-to (iso {A} {[]}) {()}
_≅_.from-to (iso {A} {_ :: _}) {fzero} = refl
_≅_.from-to (iso {A} {_ :: _}) {fsucc i} rewrite (_≅_.from-to iso) {i} = refl
