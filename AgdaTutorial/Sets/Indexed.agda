module Sets.Indexed where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc)

data Fin : ℕ → Set where
    zero : (n : ℕ) → Fin (suc n)
    suc  : {n : ℕ} → Fin n → Fin (suc n)

data OnlyTrue : Bool → Set where
    true : OnlyTrue true

data OnlyEven : ℕ → Set where
    zero : OnlyEven 0
    add2 : {n : ℕ} → OnlyEven n → OnlyEven (suc (suc n))

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)

data Indexed (A B : Set) : Bool → Set where
    false : A → Indexed A B false
    true : B → Indexed A B true

