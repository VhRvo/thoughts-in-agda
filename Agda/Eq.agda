module Eq where

import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl)

-- data Nat : Set where
--     zero : Nat
--     succ : Nat → Nat

-- symm : {A : Set} → {a b : A} → a ≡ b → b ≡ a
-- symm refl = refl

module Eq1 where
    data _≡_ {A : Set} : A → A → Set where
        refl : (a : A) → a ≡ a

    symm : ∀ {A : Set} (x y : A) → x ≡ y → y ≡ x
    symm .a .a (refl a) = refl a

module Eq2 where
    data _≡_ {A : Set} (a : A) : A → Set where
        refl : a ≡ a

    symm : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    symm {_} {x} {.x} refl = refl



Fibrational Induction Rules for Initial Algebras 

Neil Ghani, Patricia Johann, and Cl´ement Fumex
