{-# OPTIONS --without-K --safe #-}

module Any where

record AnyT (T : Set → Set) : Set₁ where
  field Any : {A : Set} → (A → Set) → T A → Set
