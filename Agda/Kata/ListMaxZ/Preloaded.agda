{-# OPTIONS --safe #-}
module Preloaded where
    open import Data.List
    open import Data.Integer

    list-max-ℤ : List ℤ → ℤ
    list-max-ℤ xs = foldr _⊔_ (+ 0) xs
