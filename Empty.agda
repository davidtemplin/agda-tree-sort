{-# OPTIONS --without-K --safe #-}

module Empty where

data ⊥ : Set where

⊥-elim : ∀ {P : Set} → ⊥ → P
⊥-elim ()
