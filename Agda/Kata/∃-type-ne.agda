{-# OPTIONS --safe #-}
module ∃-type-ne where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Function.Base using (id)

void : Set → Set
void A = A → ⊥

∃-type-ne : ∃ λ (A : Set) → ∃ λ B → A ≢ B
∃-type-ne = ⊥ , ⊤ , (λ eq → (subst void eq id) tt)
