{-# OPTIONS --without-K --safe #-}

module Implication where

open import Functions using (id ; _∘_)
open import Product using (_×_ ; ⟨_,_⟩)
open import Unit using (⊤); open Unit.⊤

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

×-cong : ∀ {X Y X' Y' : Set} → (X → X') → (Y → Y') → (X × Y) → (X' × Y')
×-cong f g ⟨ x , y ⟩ = ⟨ f x , g y ⟩

×-assoc : ∀ {X Y Z : Set} → (X × Y) × Z → X × (Y × Z)
×-assoc ⟨ ⟨ x , y ⟩ , z ⟩ = ⟨ x , ⟨ y , z ⟩ ⟩

⊤-left : ∀ {X : Set} → X → ⊤ × X
⊤-left x = ⟨ ⊤.* , x ⟩

⊤-right : ∀ {X : Set} → X → X × ⊤
⊤-right x = ⟨ x , ⊤.* ⟩
