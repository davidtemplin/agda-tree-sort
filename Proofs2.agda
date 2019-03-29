{-# OPTIONS --without-K --safe #-}

open import Bool using (Bool); open Bool.Bool
open import Equality using (_≡_ ; _≢_ ; ≡-symmetric ; ≡-transitive)
open import Implication using (_→⟨_⟩_ ; _∎ ; _↔_ ; ×-cong ; ×-assoc ; ⊤-left ; ⊤-right)
open import Relation using (TotalOrder ; total-order-reflexive ; CharacteristicFunction)
open import Sum using (_+_); open Sum._+_

module Proofs2
  (A : Set)
  (_≤_ : A → A → Set)
  (_≤?_ : A → A → Bool)
  (≤?-characteristic-function : CharacteristicFunction _≤_ _≤?_)
  (≤-total-order : TotalOrder _≤_) where

open import Empty using (⊥ ; ⊥-elim)
open import Fin renaming (_≤_ to _≤-Fin_)
open import Functions using (_$_ ; id ; _∘_ ; uncurry ; _&_)
open import Inspect using (inspect ; [_])
open import List using (List ; _++_ ; length ; lookup); open List.List

open import Product using (_×_ ; ⟨_,_⟩); open Product.∃
import Sorted; module S = Sorted A _≤_ ≤-total-order; open S using (SortedT ; A⁺ ; -∞ ; ∞ ; ⟦_⟧ ; _≤⁺⟦_⟧≤⁺_ ; _≤⁺_ ; -∞≤⁺⟦a⟧≤⁺∞ ; weaken-low ; strengthen-low ; weaken-high ; ≤⁺-total-order ; Sorted-++ ; head-min) ; open S.SortedT ⦃...⦄ ; open S._≤⁺_
open import Tree using (Tree); open Tree.Tree
open import TreeSort A _≤?_ using (tree-sort ; to-search-tree ; insert ; flatten)
open import Unit using (⊤)

≤?-total : ∀ {a₁ a₂ : A} → a₁ ≤? a₂ ≡ false → a₂ ≤? a₁ ≡ true
≤?-total {a₁} {a₂} a₁≤?a₂≡false with TotalOrder.total ≤-total-order {a₁} {a₂}
... | left  a₁≤a₂ = ⊥-elim contradiction
  where
    a₁≤?a₂≡true : a₁ ≤? a₂ ≡ true
    a₁≤?a₂≡true = _↔_.from ≤?-characteristic-function a₁≤a₂

    true≡a₁≤?a₂ : true ≡ a₁ ≤? a₂
    true≡a₁≤?a₂ = ≡-symmetric a₁≤?a₂≡true

    true≡false : true ≡ false
    true≡false = ≡-transitive true≡a₁≤?a₂ a₁≤?a₂≡false

    true≢false : true ≢ false
    true≢false ()

    contradiction : ⊥
    contradiction = true≢false true≡false
... | right a₂≤a₁ = _↔_.from ≤?-characteristic-function a₂≤a₁

insert-preserves-sort : ∀ {low high : A⁺} {t : Tree A} {a : A} → low ≤⁺⟦ a ⟧≤⁺ high → Sorted low high t → Sorted low high (insert a t)
insert-preserves-sort {low} {high} {empty} {a} low≤⁺⟦a⟧≤⁺high _ = low≤⁺⟦a⟧≤⁺high &
  low ≤⁺⟦ a ⟧≤⁺ high                                                 →⟨ ⊤-right ⟩
  low ≤⁺⟦ a ⟧≤⁺ high × ⊤                                             →⟨ ⊤-left ⟩
  ⊤ × low ≤⁺⟦ a ⟧≤⁺ high × ⊤                                         →⟨ id ⟩
  Sorted low high empty × low ≤⁺⟦ a ⟧≤⁺ high × Sorted low high empty →⟨ id ⟩
  Sorted low high (node empty a empty)                               →⟨ id ⟩
  Sorted low high (insert a empty)                                   ∎
insert-preserves-sort {low} {high} {node l a' r} {a} ⟨ low≤⁺⟦a⟧ , ⟦a⟧≤⁺high ⟩ p₂ with a ≤? a' | inspect (a ≤?_) a'
... | true | [ a≤?a'≡true ] = p₂ &
  Sorted low high (node l a' r)                                               →⟨ id ⟩
  Sorted low ⟦ a' ⟧ l × low ≤⁺⟦ a' ⟧≤⁺ high × Sorted ⟦ a' ⟧ high r            →⟨ ×-cong (insert-preserves-sort low≤⁺⟦a⟧≤⁺⟦a'⟧) id ⟩
  Sorted low ⟦ a' ⟧ (insert a l) × low ≤⁺⟦ a' ⟧≤⁺ high × Sorted ⟦ a' ⟧ high r →⟨ id ⟩
  Sorted low high (node (insert a l) a' r)                                    ∎
  where
    a≤a' : a ≤ a'
    a≤a' = _↔_.to ≤?-characteristic-function a≤?a'≡true

    ⟦a⟧≤⁺⟦a'⟧ : ⟦ a ⟧ ≤⁺ ⟦ a' ⟧
    ⟦a⟧≤⁺⟦a'⟧ = ≤⁺-lift a≤a'
    
    low≤⁺⟦a⟧≤⁺⟦a'⟧ : low ≤⁺⟦ a ⟧≤⁺ ⟦ a' ⟧
    low≤⁺⟦a⟧≤⁺⟦a'⟧ = ⟨ low≤⁺⟦a⟧ , ⟦a⟧≤⁺⟦a'⟧ ⟩
    
... | false | [ a≤?a'≡false ] = p₂ &
  Sorted low high (node l a' r)                                               →⟨ id ⟩
  Sorted low ⟦ a' ⟧ l × low ≤⁺⟦ a' ⟧≤⁺ high × Sorted ⟦ a' ⟧ high r            →⟨ ×-cong id $ ×-cong id $ insert-preserves-sort ⟦a'⟧≤⁺⟦a⟧≤⁺high ⟩
  Sorted low ⟦ a' ⟧ l × low ≤⁺⟦ a' ⟧≤⁺ high × Sorted ⟦ a' ⟧ high (insert a r) →⟨ id ⟩
  Sorted low high (node l a' (insert a r))                                    ∎
  where
    a'≤?a≡true : a' ≤? a ≡ true
    a'≤?a≡true = ≤?-total a≤?a'≡false

    a'≤a : a' ≤ a
    a'≤a = _↔_.to ≤?-characteristic-function a'≤?a≡true

    ⟦a'⟧≤⁺⟦a⟧ : ⟦ a' ⟧ ≤⁺ ⟦ a ⟧
    ⟦a'⟧≤⁺⟦a⟧ = ≤⁺-lift a'≤a
    
    ⟦a'⟧≤⁺⟦a⟧≤⁺high : ⟦ a' ⟧ ≤⁺⟦ a ⟧≤⁺ high
    ⟦a'⟧≤⁺⟦a⟧≤⁺high = ⟨ ⟦a'⟧≤⁺⟦a⟧ , ⟦a⟧≤⁺high ⟩
    
to-search-tree-sorted : ∀ {as : List A} → Sorted -∞ ∞ (to-search-tree as)
to-search-tree-sorted {[]} = ⊤.*
to-search-tree-sorted {a :: as} = insert-preserves-sort -∞≤⁺⟦a⟧≤⁺∞ $ to-search-tree-sorted {as}

flatten-preserves-sort : ∀ {low high : A⁺} → {t : Tree A} → Sorted low high t → Sorted low high (flatten t)
flatten-preserves-sort {low} {high} {empty} p = ⊤.*
flatten-preserves-sort {low} {high} {node l a r} p = p &
  Sorted low high (node l a r)                                                        →⟨ id ⟩
  Sorted low ⟦ a ⟧ l × low ≤⁺⟦ a ⟧≤⁺ high × Sorted ⟦ a ⟧ high r                       →⟨ ×-cong (flatten-preserves-sort {low} {⟦ a ⟧} {l}) (×-cong id (flatten-preserves-sort {⟦ a ⟧} {high} {r})) ⟩
  Sorted low ⟦ a ⟧ (flatten l) × low ≤⁺⟦ a ⟧≤⁺ high × Sorted ⟦ a ⟧ high (flatten r)   →⟨ ×-cong id $ ×-cong strengthen-low id ⟩
  Sorted low ⟦ a ⟧ (flatten l) × ⟦ a ⟧ ≤⁺⟦ a ⟧≤⁺ high × Sorted ⟦ a ⟧ high (flatten r) →⟨ id ⟩
  Sorted low ⟦ a ⟧ (flatten l) × Sorted ⟦ a ⟧ high (a :: flatten r)                   →⟨ uncurry $ Sorted-++ low≤⁺⟦a⟧ ⟦a⟧≤⁺⟦a⟧ ⟦a⟧≤⁺high ⟩
  Sorted low high (flatten l ++ a :: flatten r)                                       →⟨ id ⟩
  Sorted low high (flatten (node l a r))                                              ∎
  where
    low≤⁺⟦a⟧ : low ≤⁺ ⟦ a ⟧
    low≤⁺⟦a⟧ = proj₁ $ proj₁ $ proj₂ p

    ⟦a⟧≤⁺high : ⟦ a ⟧ ≤⁺ high
    ⟦a⟧≤⁺high = proj₂ $ proj₁ $ proj₂ p

    ⟦a⟧≤⁺⟦a⟧ : ⟦ a ⟧ ≤⁺ ⟦ a ⟧
    ⟦a⟧≤⁺⟦a⟧ = ≤⁺-lift $ total-order-reflexive ≤-total-order
    
tree-sort-sorts : ∀ {as : List A} → Sorted -∞ ∞ (tree-sort as)
tree-sort-sorts {as} = flatten-preserves-sort $ to-search-tree-sorted {as}

Sorted' : List A → Set
Sorted' as = ∀ {i₁ i₂ : Fin (length as)} → i₁ ≤-Fin i₂ → lookup as i₁ ≤ lookup as i₂

sound : ∀ {as : List A} → Sorted -∞ ∞ as → Sorted' as
sound {[]} _ ()
sound {a :: as} s (fzero-min {.(length as)} {i}) = head-min {as} {a} {i} s
sound {a :: as} ⟨ _ , s ⟩ (fsucc≤fsucc p) = sound (weaken-low -∞-min s) p

tree-sort-really-sorts : ∀ {as : List A} → Sorted' (tree-sort as)
tree-sort-really-sorts {as} = sound $ tree-sort-sorts {as}
