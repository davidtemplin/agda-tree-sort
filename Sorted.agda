{-# OPTIONS --without-K --safe #-}

module Sorted (A : Set) (_≤_ : A → A → Set) where

open import List using (List); open List.List
open import Product using (_×_)
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
