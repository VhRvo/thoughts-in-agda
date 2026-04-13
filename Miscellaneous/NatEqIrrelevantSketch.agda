{-# OPTIONS --without-K --safe #-}

module Miscellaneous.NatEqIrrelevantSketch where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)  -- : (m n : ℕ) → Dec (m ≡ n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

normalize : ∀ {m n : ℕ} → (m ≡ n) → (m ≡ n)
normalize {m} {n} p with m ≟ n
... | yes q = q
... | no ¬q = ⊥-elim (¬q p)
