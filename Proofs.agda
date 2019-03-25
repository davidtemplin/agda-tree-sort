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
open import Isomorphism using (_≅_ ; _≅⟨_⟩_ ; _∎ ; ≅-reflexive ; ≅-transitive ; ≅-symmetric)
open import List using (List ; _++_ ; length ; lookup); open List.List
open import Membership using (_∈_)
open import Permutation using (_≈_)
open import Product using (∃ ; ⟨_,_⟩); open Product.∃
open import Sum using (_+_); open Sum._+_
open import Tree; open Tree.Tree
open import TreeSort A _≤?_ using (tree-sort; to-search-tree; flatten; insert)

empty≈[] : ∀ {a : A} → (a ∈ empty) ≅ (a ∈ [])
_≅_.to empty≈[] ()
_≅_.from empty≈[] ()
_≅_.to-from empty≈[] {()}
_≅_.from-to empty≈[] {()}

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

⊥-left : ∀ {X : Set} → X ≅ ⊥ + X
_≅_.to ⊥-left = right
_≅_.from ⊥-left (left ())
_≅_.from ⊥-left (right x) = x
_≅_.to-from ⊥-left {left ()}
_≅_.to-from ⊥-left {right x} = refl
_≅_.from-to ⊥-left {x} = refl

∈-distr-++ : ∀ {x : A} {as₁ as₂ : List A} → (x ∈ (as₁ ++ as₂)) ≅ (x ∈ as₁ + x ∈ as₂)
∈-distr-++ {x} {[]} {as₂} =
  x ∈ ([] ++ as₂)    ≅⟨ ≅-reflexive ⟩
  x ∈ as₂            ≅⟨ ⊥-left ⟩
  ⊥ + x ∈ as₂        ≅⟨ ≅-reflexive ⟩
  (x ∈ [] + x ∈ as₂) ∎
∈-distr-++ {x} {a :: as₁} {as₂} =
  x ∈ (a :: as₁ ++ as₂)         ≅⟨ ≅-reflexive ⟩
  a ≡ x + x ∈ (as₁ ++ as₂)      ≅⟨ +-cong-right ∈-distr-++ ⟩
  a ≡ x + x ∈ as₁ + x ∈ as₂     ≅⟨ +-assoc  ⟩
  (a ≡ x + x ∈ as₁) + x ∈ as₂   ≅⟨ ≅-reflexive ⟩
  (x ∈ (a :: as₁) + x ∈ as₂)    ∎

flatten-lemma : ∀ {t : Tree A} → t ≈ flatten t
flatten-lemma {empty} {a} = empty≈[] {a}
flatten-lemma {node l a r} {x} =
  x ∈ node l a r                        ≅⟨ ≅-reflexive ⟩
  x ∈ l + a ≡ x + x ∈ r                 ≅⟨ +-cong flatten-lemma (+-cong-right flatten-lemma) ⟩
  x ∈ flatten l + a ≡ x + x ∈ flatten r ≅⟨ ≅-reflexive ⟩
  x ∈ flatten l + x ∈ a :: flatten r    ≅⟨ ≅-symmetric ∈-distr-++ ⟩
  x ∈ (flatten l ++ (a :: flatten r))   ≅⟨ ≅-reflexive ⟩
  x ∈ flatten (node l a r)              ∎

empty-lemma : ∀ {as : List A} → as ≈ empty → as ≡ []
empty-lemma {[]} _ = refl
empty-lemma {_ :: _} p = ⊥-elim $ _≅_.to p $ left refl

singleton-lemma : ∀ {a : A} → a :: [] ≈ node empty a empty
singleton-lemma {a} {x} =
  x ∈ a :: []            ≅⟨ ≅-reflexive ⟩
  a ≡ x + ⊥              ≅⟨ ⊥-left ⟩
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

iso : ∀ {as : List A} → Fin (length as) ≅ ∃ A (λ a → a ∈ as)
_≅_.to (iso {[]}) ()
_≅_.to (iso {a :: _}) fzero = ⟨ a , left refl ⟩
_≅_.to (iso {_ :: _}) (fsucc i) = let r = _≅_.to iso i in ⟨ proj₁ r , right (proj₂ r) ⟩
_≅_.from (iso {[]}) ()
_≅_.from (iso {_ :: _}) ⟨ _ , left _ ⟩ = fzero
_≅_.from (iso {_ :: _}) ⟨ a' , right x ⟩ = fsucc (_≅_.from iso ⟨ a' , x ⟩)
_≅_.to-from (iso {[]}) {()}
_≅_.to-from (iso {_ :: _}) {⟨ _ , left refl ⟩} = refl
_≅_.to-from (iso {_ :: _}) {⟨ a' , right x ⟩} rewrite (_≅_.to-from iso) {⟨ a' , x ⟩} = refl
_≅_.from-to (iso {[]}) {()}
_≅_.from-to (iso {_ :: _}) {fzero} = refl
_≅_.from-to (iso {_ :: _}) {fsucc i} rewrite (_≅_.from-to iso) {i} = refl

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

lookup-same : ∀ {as₁ as₂ : List A} {i : Fin (length as₁)} → (p : as₁ ≈ as₂) → lookup as₁ i ≡ lookup as₂ (_≅_.to (sound-iso p) i)
lookup-same {as₁} {as₂} {i} p =
  lookup as₁ i                                                 ≡⟨ lookup-eq {as₁} ⟩
  lookup' as₁ (_≅_.to iso i)                                   ≡⟨ lookup'-eq p ⟩
  lookup' as₂ (_≅_.to (∃-cong p) $ _≅_.to iso i)               ≡⟨ lookup-eq-2 {as₂}  ⟩
  lookup as₂ (_≅_.from iso $ _≅_.to (∃-cong p) $ _≅_.to iso i) ≡⟨ refl ⟩
  lookup as₂ (_≅_.to (sound-iso p) i)                          ∎-eq

sound : ∀ {as₁ as₂ : List A} → as₁ ≈ as₂ → as₁ ≈' as₂
sound {as₁} {as₂} p = record
  {
    isomorphism = sound-iso p ;
    lookup-same = lookup-same p
  }
