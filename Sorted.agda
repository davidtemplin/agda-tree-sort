{-# OPTIONS --without-K --safe #-}

open import Relation using (TotalOrder ; Reflexive ; total-order-reflexive)

module Sorted (A : Set) (_≤_ : A → A → Set) (≤-total-order : TotalOrder _≤_) where

open import Equality using (_≡_); open Equality._≡_
open import Fin using (Fin); open Fin.Fin
open import Functions using (_$_ ; id ; _&_ ; uncurry)
open import Implication using (_→⟨_⟩_ ; _∎ ; ×-cong ; ×-assoc)
open import List using (List ; _++_ ; lookup ; length); open List.List
open import Product using (_×_ ; ⟨_,_⟩); open Product.∃
open import Sum using (_+_); open Sum._+_
open import Tree using (Tree); open Tree.Tree
open import Unit using (⊤)

data A⁺ : Set where
  -∞  : A⁺
  ∞   : A⁺
  ⟦_⟧ : A → A⁺

data _≤⁺_ : A⁺ → A⁺ → Set where
  -∞-min  : ∀ {e : A⁺} → -∞ ≤⁺ e
  ∞-max   : ∀ {e : A⁺} → e ≤⁺ ∞
  ≤⁺-lift : ∀ {a₁ a₂ : A} → a₁ ≤ a₂ → ⟦ a₁ ⟧ ≤⁺ ⟦ a₂ ⟧

_≤⁺⟦_⟧≤⁺_ : A⁺ → A → A⁺ → Set
low ≤⁺⟦ a ⟧≤⁺ high = (low ≤⁺ ⟦ a ⟧) × (⟦ a ⟧ ≤⁺ high)

-∞≤⁺⟦a⟧≤⁺∞ : ∀ {a : A} → -∞ ≤⁺⟦ a ⟧≤⁺ ∞
-∞≤⁺⟦a⟧≤⁺∞ = ⟨ -∞-min , ∞-max ⟩

≤⁺-total-order : TotalOrder _≤⁺_

TotalOrder.antisymmetric ≤⁺-total-order {.-∞} {.-∞} -∞-min -∞-min = refl
TotalOrder.antisymmetric ≤⁺-total-order {.∞} {.∞} ∞-max ∞-max = refl
TotalOrder.antisymmetric ≤⁺-total-order {.(⟦ _ ⟧)} {.(⟦ _ ⟧)} (≤⁺-lift x₁) (≤⁺-lift x₂) rewrite TotalOrder.antisymmetric ≤-total-order x₁ x₂ = refl

TotalOrder.transitive ≤⁺-total-order {.-∞} {_} {_} -∞-min _ = -∞-min
TotalOrder.transitive ≤⁺-total-order {_} {.∞} {.∞} ∞-max ∞-max = ∞-max
TotalOrder.transitive ≤⁺-total-order {.(⟦ _ ⟧)} {.(⟦ _ ⟧)} {.∞} (≤⁺-lift _) ∞-max = ∞-max
TotalOrder.transitive ≤⁺-total-order {.(⟦ _ ⟧)} {.(⟦ _ ⟧)} {.(⟦ _ ⟧)} (≤⁺-lift x₁) (≤⁺-lift x₂) = ≤⁺-lift $ TotalOrder.transitive ≤-total-order x₁ x₂

TotalOrder.total ≤⁺-total-order { -∞} {_} = left -∞-min
TotalOrder.total ≤⁺-total-order {∞} {_} = right ∞-max
TotalOrder.total ≤⁺-total-order {⟦ x ⟧} { -∞} = right -∞-min
TotalOrder.total ≤⁺-total-order {⟦ x ⟧} {∞} = left ∞-max
TotalOrder.total ≤⁺-total-order {⟦ x₁ ⟧} {⟦ x₂ ⟧} with TotalOrder.total ≤-total-order {x₁} {x₂}
... | left x₁≤x₂ = left $ ≤⁺-lift x₁≤x₂
... | right x₂≤x₁ = right $ ≤⁺-lift x₂≤x₁

≤⁺-reflexive : Reflexive _≤⁺_
≤⁺-reflexive { -∞} = -∞-min
≤⁺-reflexive {∞} = ∞-max
≤⁺-reflexive {⟦ a ⟧} = ≤⁺-lift $ total-order-reflexive ≤-total-order {a}

record SortedT (T : Set → Set) : Set₁ where                                                                                                                                                                                                  
  field Sorted : A⁺ → A⁺ → T A → Set

open SortedT ⦃...⦄

instance
  SortedList : SortedT List
  Sorted ⦃ SortedList ⦄ = SortedListImpl
    where
      SortedListImpl : A⁺ → A⁺ → List A → Set
      SortedListImpl low high []        = ⊤
      SortedListImpl low high (a :: as) = low ≤⁺⟦ a ⟧≤⁺ high × SortedListImpl ⟦ a ⟧ high as

instance
  SortedTree : SortedT Tree
  Sorted ⦃ SortedTree ⦄ = SortedTreeImpl
    where
      SortedTreeImpl : A⁺ → A⁺ → Tree A → Set
      SortedTreeImpl low high empty = ⊤
      SortedTreeImpl low high (node l a r) = SortedTreeImpl low ⟦ a ⟧ l × low ≤⁺⟦ a ⟧≤⁺ high × SortedTreeImpl ⟦ a ⟧ high r

weaken-low' : ∀ {low₁ low₂ high : A⁺} {a : A} → low₂ ≤⁺ low₁ → low₁ ≤⁺⟦ a ⟧≤⁺ high → low₂ ≤⁺⟦ a ⟧≤⁺ high
weaken-low' {low₁} {low₂} {high} {a} low₂≤⁺low₁ ⟨ low₁≤⁺⟦a⟧ , ⟦a⟧≤⁺high ⟩ = ⟨ TotalOrder.transitive ≤⁺-total-order low₂≤⁺low₁ low₁≤⁺⟦a⟧ , ⟦a⟧≤⁺high ⟩

weaken-low : ∀ {low₁ low₂ high : A⁺} {as : List A} → low₂ ≤⁺ low₁ → Sorted low₁ high as → Sorted low₂ high as
weaken-low {low₁} {low₂} {high} {[]} low₂≤⁺low₁ s = ⊤.*
weaken-low {low₁} {low₂} {high} {a :: as} low₂≤⁺low₁ =
  Sorted low₁ high (a :: as)                 →⟨ id ⟩
  low₁ ≤⁺⟦ a ⟧≤⁺ high × Sorted ⟦ a ⟧ high as →⟨ ×-cong (weaken-low' low₂≤⁺low₁) id ⟩
  low₂ ≤⁺⟦ a ⟧≤⁺ high × Sorted ⟦ a ⟧ high as →⟨ id ⟩
  Sorted low₂ high (a :: as)                 ∎

strengthen-low : ∀ {low high : A⁺} {a : A} → low ≤⁺⟦ a ⟧≤⁺ high → ⟦ a ⟧ ≤⁺⟦ a ⟧≤⁺ high
strengthen-low ⟨ _ , ⟦a⟧≤⁺high ⟩ = ⟨ ≤⁺-lift $ total-order-reflexive ≤-total-order , ⟦a⟧≤⁺high ⟩

weaken-high : ∀ {low high₁ high₂ : A⁺} {a : A} → high₁ ≤⁺ high₂ → low ≤⁺⟦ a ⟧≤⁺ high₁ → low ≤⁺⟦ a ⟧≤⁺ high₂
weaken-high high₁≤⁺high₂ ⟨ low≤⁺⟦a⟧ , ⟦a⟧≤⁺high₁ ⟩ = ⟨ low≤⁺⟦a⟧ , TotalOrder.transitive ≤⁺-total-order ⟦a⟧≤⁺high₁ high₁≤⁺high₂ ⟩

Sorted-++ : ∀ {low₁ high₁ low₂ high₂ : A⁺} {as₁ as₂ : List A} → low₁ ≤⁺ high₁ → high₁ ≤⁺ low₂ → low₂ ≤⁺ high₂ → Sorted low₁ high₁ as₁ → Sorted low₂ high₂ as₂ → Sorted low₁ high₂ (as₁ ++ as₂)
Sorted-++ {low₁} {high₁} {low₂} {high₂} {[]} {as₂} low₁≤⁺high₁ high₁≤⁺low₂ low₂≤⁺high₂ s₁ s₂ = weaken-low (TotalOrder.transitive ≤⁺-total-order low₁≤⁺high₁ high₁≤⁺low₂) s₂
Sorted-++ {low₁} {high₁} {low₂} {high₂} {a :: as₁} {as₂} low₁≤⁺high₁ high₁≤⁺low₂ low₂≤⁺high₂ s₁ s₂ = ⟨ s₁ , s₂ ⟩ &
  Sorted low₁ high₁ (a :: as₁) × Sorted low₂ high₂ as₂                    →⟨ id ⟩
  (low₁ ≤⁺⟦ a ⟧≤⁺ high₁ × Sorted ⟦ a ⟧ high₁ as₁) × Sorted low₂ high₂ as₂ →⟨ ×-assoc ⟩
  low₁ ≤⁺⟦ a ⟧≤⁺ high₁ × Sorted ⟦ a ⟧ high₁ as₁ × Sorted low₂ high₂ as₂   →⟨ ×-cong id $ uncurry $ Sorted-++ ⟦a⟧≤⁺high₁ high₁≤⁺low₂ low₂≤⁺high₂ ⟩
  low₁ ≤⁺⟦ a ⟧≤⁺ high₁ × Sorted ⟦ a ⟧ high₂ (as₁ ++ as₂)                  →⟨ ×-cong (weaken-high high₁≤⁺high₂) id ⟩
  low₁ ≤⁺⟦ a ⟧≤⁺ high₂ × Sorted ⟦ a ⟧ high₂ (as₁ ++ as₂)                  →⟨ id ⟩
  Sorted low₁ high₂ (a :: (as₁ ++ as₂))                                   →⟨ id ⟩
  Sorted low₁ high₂ ((a :: as₁) ++ as₂)                                   ∎
  where
    ⟦a⟧≤⁺high₁ : ⟦ a ⟧ ≤⁺ high₁
    ⟦a⟧≤⁺high₁ = proj₂ $ proj₁ s₁

    high₁≤⁺high₂ : high₁ ≤⁺ high₂
    high₁≤⁺high₂ = TotalOrder.transitive ≤⁺-total-order high₁≤⁺low₂ low₂≤⁺high₂

head-min : ∀ {as : List A} {a : A} {i : Fin (length (a :: as))} → Sorted -∞ ∞ (a :: as) → a ≤ lookup (a :: as) i
head-min {[]} {_} {fzero} _ = total-order-reflexive ≤-total-order
head-min {[]} {_} {fsucc ()}
head-min {_ :: _} {_} {fzero} _ = total-order-reflexive ≤-total-order
head-min {a' :: as} {a} {fsucc i} s = TotalOrder.transitive ≤-total-order a≤a' $ head-min {as} {a'} {i} (weaken-low -∞-min Sorted-a'::as)
  where
    Sorted-a'::as : Sorted ⟦ a ⟧ ∞ (a' :: as)
    Sorted-a'::as = proj₂ s

    extract : ⟦ a ⟧ ≤⁺ ⟦ a' ⟧ → a ≤ a'
    extract (≤⁺-lift p) = p

    a≤a' : a ≤ a'
    a≤a' = extract $ proj₁ $ proj₁ $ proj₂ s
