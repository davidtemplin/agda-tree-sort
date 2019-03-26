{-# OPTIONS --without-K --safe #-}

-- TODO:
--   * fix precedence of operators in order to eliminate parentheses, etc.
--   * eliminate / combine lemmas
--   * simplify proofs

open import Bool using (Bool); open Bool.Bool

module Proofs (A : Set) (_≤?_ : A → A → Bool) where

open import Empty using (⊥ ; ⊥-elim)
open import Equality using (_≡_ ; _≡⟨_⟩_) renaming (_∎ to _∎-eq); open Equality._≡_
open import Fin using (Fin); open Fin.Fin
open import Functions using (_∘_ ; _$_)
open import Inspect using (inspect ; [_])
open import Isomorphism using (_≅_ ; _≅⟨_⟩_ ; _∎ ; ≅-reflexive ; ≅-transitive ; ≅-symmetric ; +-cong-left ; +-cong-right ; +-cong ; +-comm ; +-assoc ; ∈-distr-++ ; ⊥-left-unit)
open import List using (List ; _++_ ; length ; lookup); open List.List
open import Membership using (_∈_)
open import Permutation A using (_≈_ ; empty≈[] ; empty-lemma ; singleton-lemma ; ::-cong ; ++-cong-left ; ++-cong-right ; shift-lemma ; swap-lemma ; sound-iso ; lookup-match)
open import Product using (∃ ; ⟨_,_⟩); open Product.∃
open import Sum using (_+_); open Sum._+_
open import Tree; open Tree.Tree
open import TreeSort A _≤?_ using (tree-sort; to-search-tree; flatten; insert)

flatten-lemma : ∀ {t : Tree A} → t ≈ flatten t
flatten-lemma {empty} {a} = empty≈[] {a}
flatten-lemma {node l a r} {x} =
  x ∈ node l a r                        ≅⟨ ≅-reflexive ⟩
  x ∈ l + a ≡ x + x ∈ r                 ≅⟨ +-cong flatten-lemma (+-cong-right flatten-lemma) ⟩
  x ∈ flatten l + a ≡ x + x ∈ flatten r ≅⟨ ≅-reflexive ⟩
  x ∈ flatten l + x ∈ a :: flatten r    ≅⟨ ≅-symmetric ∈-distr-++ ⟩
  x ∈ (flatten l ++ (a :: flatten r))   ≅⟨ ≅-reflexive ⟩
  x ∈ flatten (node l a r)              ∎

insert-lemma : ∀ {a : A} {as : List A} {t : Tree A} → as ≈ t → a :: as ≈ insert a t
insert-lemma {a} {as} {empty} p {x} rewrite empty-lemma p = singleton-lemma
insert-lemma {a} {as} {node l a' r} p {x} with a ≤? a'
... | true  = x ∈ a :: as                                      ≅⟨ ::-cong $ ≅-transitive p flatten-lemma ⟩
              x ∈ a :: flatten (node l a' r)                   ≅⟨ ≅-reflexive ⟩
              x ∈ a :: (flatten l ++ a' :: flatten r)          ≅⟨ ≅-reflexive ⟩
              x ∈ ((a :: flatten l) ++ (a' :: flatten r))      ≅⟨ ++-cong-left $ ≅-transitive (insert-lemma $ ≅-symmetric $ flatten-lemma {l}) flatten-lemma ⟩
              x ∈ (flatten (insert a l) ++ a' :: flatten r)    ≅⟨ ≅-reflexive ⟩
              x ∈ flatten (node (insert a l) a' r)             ≅⟨ ≅-symmetric flatten-lemma ⟩
              x ∈ node (insert a l) a' r                       ∎
... | false = x ∈ a :: as                                   ≅⟨ ::-cong $ ≅-transitive p flatten-lemma ⟩
              x ∈ a :: flatten (node l a' r)                ≅⟨ ≅-reflexive ⟩
              x ∈ a :: (flatten l ++ a' :: flatten r)       ≅⟨ shift-lemma ⟩            
              x ∈ (flatten l ++ a :: a' :: flatten r)       ≅⟨ ++-cong-right swap-lemma ⟩
              x ∈ (flatten l ++ a' :: a :: flatten r)       ≅⟨ ++-cong-right $ ::-cong $ ≅-transitive (insert-lemma $ ≅-symmetric $ flatten-lemma {r}) flatten-lemma ⟩
              x ∈ (flatten l ++ a' :: flatten (insert a r)) ≅⟨ ≅-reflexive ⟩
              x ∈ flatten (node l a' (insert a r))          ≅⟨ ≅-symmetric flatten-lemma ⟩
              x ∈ node l a' (insert a r)                    ∎

to-search-tree-lemma : ∀ {as : List A} → as ≈ to-search-tree as
to-search-tree-lemma {[]} {a} =
  a ∈ []                ≅⟨ ≅-reflexive ⟩
  ⊥                     ≅⟨ ≅-reflexive ⟩
  a ∈ empty             ≅⟨ ≅-reflexive ⟩
  a ∈ to-search-tree [] ∎ 
to-search-tree-lemma {a :: as} {a'} =
  a' ∈ a :: as                      ≅⟨ insert-lemma to-search-tree-lemma ⟩
  a' ∈ insert a (to-search-tree as) ≅⟨ ≅-reflexive ⟩
  a' ∈ to-search-tree (a :: as)     ∎

tree-sort-permutes : ∀ {as : List A} → as ≈ tree-sort as
tree-sort-permutes {as} {a} =
  a ∈ as                            ≅⟨ to-search-tree-lemma ⟩
  a ∈ to-search-tree as             ≅⟨ flatten-lemma ⟩
  a ∈ flatten (to-search-tree as)   ≅⟨ ≅-reflexive ⟩
  a ∈ (flatten ∘ to-search-tree) as ≅⟨ ≅-reflexive ⟩
  a ∈ tree-sort as                  ∎                            

record _≈'_ (as₁ as₂ : List A) : Set where
  field
    isomorphism : Fin (length as₁) ≅ Fin (length as₂)
    lookup-same : ∀ {i : Fin (length as₁)} → lookup as₁ i ≡ lookup as₂ (_≅_.to isomorphism i)

sound : ∀ {as₁ as₂ : List A} → as₁ ≈ as₂ → as₁ ≈' as₂
sound {as₁} {as₂} p = record
  {
    isomorphism = sound-iso p ;
    lookup-same = lookup-match p
  }
