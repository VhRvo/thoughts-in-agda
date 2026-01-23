module Sets.Recursive where

open import Sets.Enumerated using (Bool; true; false)

data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

data ℕ⁺ : Set where
    one : ℕ⁺
    double : ℕ⁺ → ℕ⁺
    double+1 : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
    zero : ℕ₂
    id : ℕ⁺ → ℕ₂

nine : ℕ₂
nine = id (double (double (double one)))

data ℤ : Set where
    neg+1 : ℕ → ℤ
    zero : ℤ
    pos+1 : ℕ → ℤ

data BinTree : Set where
    leaf : BinTree
    node : BinTree → BinTree → BinTree

tree₁ : BinTree
tree₁ = leaf

tree₂ : BinTree
tree₂ = node tree₁ tree₁

tree₃ : BinTree
tree₃ = node tree₂ tree₂

tree₄ : BinTree
tree₄ = node (node tree₁ leaf) leaf

data BinTree₁ : Set where
    leaf : ℕ → BinTree₁
    node : BinTree₁ → BinTree₁ → BinTree₁

data BinTree₂ : Set where
    leaf : BinTree₂
    node : ℕ → BinTree₂ → BinTree₂ → BinTree₂

data BinTree₃ : Set where
    leaf : Bool → BinTree₃
    node : ℕ → BinTree₃ → BinTree₃ → BinTree₃

data List : Set where
    empty : List
    cons : ℕ → List → List

data NonEmpty : Set where
    one : NonEmpty
    cons : ℕ → NonEmpty → NonEmpty
