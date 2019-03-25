{-# OPTIONS --without-K --safe #-}

open import Bool using (Bool); open Bool.Bool

module TreeSort (A : Set) (_≤?_ : A → A → Bool) where

open import Functions using (_∘_)
open import List using (List; _++_); open List.List
open import Tree using (Tree); open Tree.Tree

insert : A → Tree A → Tree A
insert a empty        = node empty a empty
insert a (node l a' r) with a ≤? a'
... | true  = node (insert a l) a' r
... | false = node l a' (insert a r)

to-search-tree : List A → Tree A
to-search-tree []        = empty
to-search-tree (a :: as) = insert a (to-search-tree as)

flatten : Tree A → List A
flatten empty         = []
flatten (node l a r)  = flatten l ++ (a :: flatten r)

tree-sort : List A → List A
tree-sort = flatten ∘ to-search-tree
