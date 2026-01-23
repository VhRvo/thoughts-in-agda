module CommutativeMonoids where

open import Data.Nat
open import Data.Int
open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Function





data Expr n : Set where
  var : Fin n → Expr n
  _⨁_ : Expr n → Expr n → Expr n
  zero : Expr n

NF : ℕ → Set
NF = Vec ℕ

data Eqn n : Set where
  _==_ : Expr n → Expr n → Eqn n

-- eval : ∀ {n} → Expr n → NF n
-- reify : ∀ {n} → NF n → Expr n

-- norm : ∀ {n} → Expr n → Expr n
-- norm = reify ∘ eval

-- prf : ∀ n m → (n + m) + n ≡ m + (n + n)
-- prf n m = ?

