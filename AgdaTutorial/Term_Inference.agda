module Term_Inference where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Nat      using (ℕ; zero; suc)

module Normal where
    data Fin′ : ℕ → Set where
        zero : (n : _) → Fin′ (suc n)   -- ℕ is inferred
        suc  : (n : _) → Fin′ n → Fin′ (suc n)   -- ℕ is inferred

    x : Fin′ 3
    x = suc _ (zero _)   -- 2 and 1 are inferred

    data Fin : ℕ → Set where
        zero : {n : _} → Fin (suc n)
        suc  : {n : _} → Fin n → Fin (suc n)

    x′ : Fin 3
    x′ = suc {_} (zero {_})
    x″ : Fin 3
    x″ = suc zero

module Forall where
    data Fin′ : ℕ → Set where
        zero : ∀ n → Fin′ (suc n)
        suc  : ∀ n → Fin′ n → Fin′ (suc n)

    data Fin : ℕ → Set where
        zero : ∀ {n} → Fin (suc n)
        suc  : ∀ {n} → Fin n → Fin (suc n)