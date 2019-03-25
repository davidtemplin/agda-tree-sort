{-# OPTIONS --without-K --safe #-}

module Inspect where

open import Equality using (_≡_); open Equality._≡_

record Reveal_·_is_ {A : Set } {B : A → Set}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {A : Set} {B : A → Set}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]
