module LE where

open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Bool

data _≤1_ : ℕ → ℕ → Set where
  z≤n : ∀ (n : ℕ) → 0 ≤1 n
  s≤s : ∀ (m n : ℕ) → m ≤1 n → suc m ≤1 suc n

inv-z≤n : {m : ℕ} → m ≤1 0 → m ≡ 0
inv-z≤n (z≤n n) = refl

inv-z≤n'' : {m : ℕ} → m ≤1 0 → m ≡ 0
inv-z≤n'' (z≤n zero) = refl

-- inv-z≤n1 : {m : ℕ} → m ≤1 0 → m ≡ 0
-- inv-z≤n1 .(0) .(n) (z≤n n) = refl

inv-z≤n1 : {m : ℕ} → m ≤1 0 → m ≡ 0
inv-z≤n1 .{zero} (z≤n n) = refl

inv-z≤n1' : {m : ℕ} → m ≤1 0 → m ≡ 0
inv-z≤n1' .{zero} (z≤n zero) = refl

inv-z≤n2 : {m : ℕ} → m ≤1 0 → m ≡ 0
inv-z≤n2 {zero} (z≤n n) = refl

inv-z≤n2' : {m : ℕ} → m ≤1 0 → m ≡ 0
inv-z≤n2' {zero} (z≤n zero) = refl

