{-# OPTIONS --without-K --safe #-}

module Sum where

infixr 1 _+_

data _+_ (A B : Set) : Set where
  left  : A → A + B
  right : B → A + B
  
