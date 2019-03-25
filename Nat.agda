{-# OPTIONS --without-K --safe #-}

module Nat where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
