module Sets.Mutual where

open import Sets.Enumerated using (Bool; true; false)
open import Syntax.Decimal_Naturals using (ℕ; zero; suc)

data L : Set
data M : Set

data L where
    nil : L
    _::_ : ℕ → M → L

data M where
    _::_ : Bool → L → M

data Tree : Set
data List : Set

data Tree where
    node : List → Tree

data List where
    nil : List
    _::_ : Tree → List → List
