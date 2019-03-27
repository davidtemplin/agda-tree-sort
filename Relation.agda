module Relation {A : Set} where

open import Bool using (Bool); open Bool.Bool
open import Equality using (_≡_)
open import Implication using (_↔_)
open import Sum using (_+_); open Sum._+_

Relation : Set₁
Relation = A → A → Set

Reflexive : Relation → Set
Reflexive R = ∀ {a : A} → R a a

Antisymmetric : Relation → Set
Antisymmetric R = ∀ {a₁ a₂ : A} → R a₁ a₂ → R a₂ a₁ → a₁ ≡ a₂

Transitive : Relation → Set
Transitive R = ∀ {a₁ a₂ a₃ : A} → R a₁ a₂ → R a₂ a₃ → R a₁ a₃

Total : Relation → Set
Total R = ∀ {a₁ a₂ : A} → R a₁ a₂ + R a₂ a₁

record TotalOrder (R : Relation) : Set where
  field
    antisymmetric : Antisymmetric R
    transitive    : Transitive R
    total         : Total R

total-order-reflexive : ∀ {R : Relation} → TotalOrder R → Reflexive R
total-order-reflexive t {a} with TotalOrder.total t {a} {a}
... | left p  = p
... | right p = p

CharacteristicFunction : Relation → (A → A → Bool) → Set
CharacteristicFunction R c = ∀ {a₁ a₂ : A} → c a₁ a₂ ≡ true ↔ R a₁ a₂
