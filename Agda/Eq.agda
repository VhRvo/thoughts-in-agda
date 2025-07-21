module Eq where

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary

-- a = Symmetric

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

    sym : ∀ {A : Set} (x y : A) → x ≡ y → y ≡ x
    sym {_} x .x refl = refl

    trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans {_} {x} {.x} {.x} refl refl = refl

    subst : {A : Set} → {P : A → Set} → {x y : A} → x ≡ y → P x → P y
    subst {_} {_} {x} {.x} refl p = p

    cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
    cong {_} {_} {x} {.x} f refl = refl

    sym′ : ∀ {A : Set} (x y : A) → x ≡ y → y ≡ x
    sym′ x y p = subst {P = λ z → z ≡ x} p refl

    trans′ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans′ {x = x} p q = subst {P = x ≡_} q p

    cong′ : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
    cong′ {x = x} f p = subst {P = λ z → f x ≡ f z} p refl


