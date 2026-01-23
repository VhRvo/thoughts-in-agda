module Syntax.Decimal_Naturals where

data ℕ : Set where
  zero :     ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
-- {-# BUILTIN ZERO    zero #-}
-- {-# BUILTIN SUC     suc  #-}

