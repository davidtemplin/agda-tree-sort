{-# OPTIONS --without-K --safe #-}

module Functions where

open import Product using (_×_ ; ⟨_,_⟩)

infixr 1 _∘_

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ a → f (g a)

id : {A : Set} → (A → A)
id a = a

infixr 0 _$_

_$_ : {A B : Set} → (A → B) → A → B
f $ a = f a

uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
uncurry f ⟨ a , b ⟩ = f a b

infixr 0 _&_

_&_ : {A B : Set} → A → (A → B) → B
a & A→B = A→B a
