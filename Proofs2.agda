{-# OPTIONS --without-K --safe #-}

open import Bool using (Bool); open Bool.Bool
open import Equality using (_≡_ ; _≢_ ; ≡-symmetric ; ≡-transitive)
open import Implication using (_→⟨_⟩_ ; _∎ ; _↔_)
open import Sum using (_+_); open Sum._+_

module Proofs2
  (A : Set)
  (_≤_ : A → A → Set)
  (_≤?_ : A → A → Bool)
  (reflection : ∀ {a₁ a₂ : A} → (a₁ ≤? a₂ ≡ true) ↔ a₁ ≤ a₂)
  (≤-total : ∀ {a₁ a₂ : A} → ((a₁ ≤ a₂) + (a₂ ≤ a₁)))
  (≤-transitive : ∀ {a₁ a₂ a₃ : A} → a₁ ≤ a₂ → a₂ ≤ a₃ → a₁ ≤ a₃) where

open import Empty using (⊥ ; ⊥-elim)
open import Fin renaming (_≤_ to _≤-Fin_)
open import Functions using (_$_ ; id ; _∘_ ; uncurry ; _&_)
open import Inspect using (inspect ; [_])
open import List using (List ; _++_ ; length ; lookup); open List.List

open import Product using (_×_ ; ⟨_,_⟩); open Product.∃
import Sorted; module S = Sorted A _≤_; open S using (SortedT ; A⁺ ; -∞ ; ∞ ; ⟦_⟧ ; _≤⁺⟦_⟧≤⁺_ ; _≤⁺_) ; open S.SortedT ⦃...⦄ ; open S._≤⁺_
open import Tree using (Tree); open Tree.Tree
open import TreeSort A _≤?_ using (tree-sort ; to-search-tree ; insert ; flatten)
open import Unit using (⊤)

×-cong : ∀ {X Y X' Y' : Set} → (X → X') → (Y → Y') → (X × Y) → (X' × Y')
×-cong f g ⟨ x , y ⟩ = ⟨ f x , g y ⟩

×-assoc : ∀ {X Y Z : Set} → (X × Y) × Z → X × (Y × Z)
×-assoc ⟨ ⟨ x , y ⟩ , z ⟩ = ⟨ x , ⟨ y , z ⟩ ⟩

-∞≤⁺⟦a⟧≤⁺∞ : ∀ {a : A} → -∞ ≤⁺⟦ a ⟧≤⁺ ∞
-∞≤⁺⟦a⟧≤⁺∞ = ⟨ -∞-min , ∞-max ⟩

≤-reflexive : ∀ {a : A} → a ≤ a
≤-reflexive {a} with ≤-total {a} {a}
... | left a≤a  = a≤a
... | right a≤a = a≤a

≤⁺-transitive : ∀ {e₁ e₂ e₃ : A⁺} → e₁ ≤⁺ e₂ → e₂ ≤⁺ e₃ → e₁ ≤⁺ e₃
≤⁺-transitive {.-∞} {_} {_} -∞-min _ = -∞-min
≤⁺-transitive {_} {.∞} {.∞} ∞-max ∞-max = ∞-max
≤⁺-transitive {.(⟦ _ ⟧)} {.(⟦ _ ⟧)} {.∞} (≤⁺-lift _) ∞-max = ∞-max
≤⁺-transitive {.(⟦ _ ⟧)} {.(⟦ _ ⟧)} {.(⟦ _ ⟧)} (≤⁺-lift x₁) (≤⁺-lift x₂) = ≤⁺-lift $ ≤-transitive x₁ x₂

weaken-low' : ∀ {low₁ low₂ high : A⁺} {a : A} → low₂ ≤⁺ low₁ → low₁ ≤⁺⟦ a ⟧≤⁺ high → low₂ ≤⁺⟦ a ⟧≤⁺ high
weaken-low' {low₁} {low₂} {high} {a} low₂≤⁺low₁ ⟨ low₁≤⁺⟦a⟧ , ⟦a⟧≤⁺high ⟩ = ⟨ ≤⁺-transitive low₂≤⁺low₁ low₁≤⁺⟦a⟧ , ⟦a⟧≤⁺high ⟩

weaken-low : ∀ {low₁ low₂ high : A⁺} {as : List A} → low₂ ≤⁺ low₁ → Sorted low₁ high as → Sorted low₂ high as
weaken-low {low₁} {low₂} {high} {[]} low₂≤⁺low₁ s = ⊤.*
weaken-low {low₁} {low₂} {high} {a :: as} low₂≤⁺low₁ =
  Sorted low₁ high (a :: as)                 →⟨ id ⟩
  low₁ ≤⁺⟦ a ⟧≤⁺ high × Sorted ⟦ a ⟧ high as →⟨ ×-cong (weaken-low' low₂≤⁺low₁) id ⟩
  low₂ ≤⁺⟦ a ⟧≤⁺ high × Sorted ⟦ a ⟧ high as →⟨ id ⟩
  Sorted low₂ high (a :: as)                 ∎

strengthen-low : ∀ {low high : A⁺} {a : A} → low ≤⁺⟦ a ⟧≤⁺ high → ⟦ a ⟧ ≤⁺⟦ a ⟧≤⁺ high
strengthen-low ⟨ _ , ⟦a⟧≤⁺high ⟩ = ⟨ ≤⁺-lift ≤-reflexive , ⟦a⟧≤⁺high ⟩

weaken-high : ∀ {low high₁ high₂ : A⁺} {a : A} → high₁ ≤⁺ high₂ → low ≤⁺⟦ a ⟧≤⁺ high₁ → low ≤⁺⟦ a ⟧≤⁺ high₂
weaken-high high₁≤⁺high₂ ⟨ low≤⁺⟦a⟧ , ⟦a⟧≤⁺high₁ ⟩ = ⟨ low≤⁺⟦a⟧ , ≤⁺-transitive ⟦a⟧≤⁺high₁ high₁≤⁺high₂ ⟩

Sorted-++ : ∀ {low₁ high₁ low₂ high₂ : A⁺} {as₁ as₂ : List A} → low₁ ≤⁺ high₁ → high₁ ≤⁺ low₂ → low₂ ≤⁺ high₂ → Sorted low₁ high₁ as₁ → Sorted low₂ high₂ as₂ → Sorted low₁ high₂ (as₁ ++ as₂)
Sorted-++ {low₁} {high₁} {low₂} {high₂} {[]} {as₂} low₁≤⁺high₁ high₁≤⁺low₂ low₂≤⁺high₂ s₁ s₂ = weaken-low (≤⁺-transitive low₁≤⁺high₁ high₁≤⁺low₂) s₂
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
    high₁≤⁺high₂ = ≤⁺-transitive high₁≤⁺low₂ low₂≤⁺high₂
    
≤?-total : ∀ {a₁ a₂ : A} → a₁ ≤? a₂ ≡ false → a₂ ≤? a₁ ≡ true
≤?-total {a₁} {a₂} a₁≤?a₂≡false with ≤-total {a₁} {a₂}
... | left  a₁≤a₂ = ⊥-elim contradiction
  where
    a₁≤?a₂≡true : a₁ ≤? a₂ ≡ true
    a₁≤?a₂≡true = _↔_.from reflection a₁≤a₂

    true≡a₁≤?a₂ : true ≡ a₁ ≤? a₂
    true≡a₁≤?a₂ = ≡-symmetric a₁≤?a₂≡true

    true≡false : true ≡ false
    true≡false = ≡-transitive true≡a₁≤?a₂ a₁≤?a₂≡false

    true≢false : true ≢ false
    true≢false ()

    contradiction : ⊥
    contradiction = true≢false true≡false
... | right a₂≤a₁ = _↔_.from reflection a₂≤a₁

⊤-left : ∀ {X : Set} → X → ⊤ × X
⊤-left x = ⟨ ⊤.* , x ⟩

⊤-right : ∀ {X : Set} → X → X × ⊤
⊤-right x = ⟨ x , ⊤.* ⟩

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
    a≤a' = _↔_.to reflection a≤?a'≡true

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
    a'≤a = _↔_.to reflection a'≤?a≡true

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
    ⟦a⟧≤⁺⟦a⟧ = ≤⁺-lift ≤-reflexive
    
tree-sort-sorts : ∀ {as : List A} → Sorted -∞ ∞ (tree-sort as)
tree-sort-sorts {as} = flatten-preserves-sort $ to-search-tree-sorted {as}

Sorted' : List A → Set
Sorted' as = ∀ {i₁ i₂ : Fin (length as)} → i₁ ≤-Fin i₂ → lookup as i₁ ≤ lookup as i₂

head-min : ∀ {as : List A} {a : A} {i : Fin (length (a :: as))} → Sorted -∞ ∞ (a :: as) → a ≤ lookup (a :: as) i
head-min {[]} {_} {fzero} _ = ≤-reflexive
head-min {[]} {_} {fsucc ()}
head-min {_ :: _} {_} {fzero} _ = ≤-reflexive
head-min {a' :: as} {a} {fsucc i} s = ≤-transitive a≤a' $ head-min {as} {a'} {i} (weaken-low -∞-min Sorted-a'::as)
  where
    Sorted-a'::as : Sorted ⟦ a ⟧ ∞ (a' :: as)
    Sorted-a'::as = proj₂ s

    extract : ⟦ a ⟧ ≤⁺ ⟦ a' ⟧ → a ≤ a'
    extract (≤⁺-lift p) = p

    a≤a' : a ≤ a'
    a≤a' = extract $ proj₁ $ proj₁ $ proj₂ s

Sound : ∀ {as : List A} → Sorted -∞ ∞ as → Sorted' as
Sound {[]} _ ()
Sound {a :: as} s (fzero-min {.(length as)} {i}) = head-min {as} {a} {i} s
Sound {a :: as} ⟨ _ , s ⟩ (fsucc≤fsucc p) = Sound (weaken-low -∞-min s) p

tree-sort-really-sorts : ∀ {as : List A} → Sorted' (tree-sort as)
tree-sort-really-sorts {as} =  Sound $ tree-sort-sorts {as}
