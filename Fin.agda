{-# OPTIONS --without-K --safe #-}

module Fin where

open import Nat using (ℕ); open Nat.ℕ

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)

data _≤_ : {n : ℕ} → Fin n → Fin n → Set where
  fzero-min   : {n : ℕ} {i : Fin (succ n)} → fzero ≤ i
  fsucc≤fsucc : {n : ℕ} {i₁ i₂ : Fin n} → i₁ ≤ i₂ → fsucc i₁ ≤ fsucc i₂
