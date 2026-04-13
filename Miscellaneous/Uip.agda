{-# OPTIONS --without-K --safe #-}

module Uip where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Properties using (≡-irrelevant)

unit-uip : (p : tt ≡ tt) → p ≡ refl
unit-uip refl = refl

one : ℕ
one = suc zero

p≡refl : (p : one ≡ one) → p ≡ refl
p≡refl p = ≡-irrelevant p refl

