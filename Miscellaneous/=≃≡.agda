{-# OPTIONS --without-K #-}

module =≃≡ where

open import Agda.Primitive public

module Martin-Löf {ℓ} {A : Set ℓ} where

  data _≡_ (a : A) : A → Set ℓ where
    refl : a ≡ a

  refexive≡ : {a : A} → a ≡ a
  refexive≡ = refl

  symmetric≡ : {a b : A} → a ≡ b → b ≡ a
  symmetric≡ {a} {.a} refl = refl

  transitive≡ : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  transitive≡ {a} {.a} {.a} refl refl = refl

open Martin-Löf public

postulate
  ext : ∀ {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} {f g : (a : A) → B a}
    → (∀ (a : A) → f a ≡ g a) → f ≡ g

module Leibniz {A : Set} where
--   _≐_ : (a b : A) → Set (lsuc lzero)
  _≐_ : (a b : A) → Set₁
  a ≐ b = (P : A → Set) → P a → P b

  reflexive≐ : {a : A} → a ≐ a
  reflexive≐ P Pa = Pa

  transitive≐ : {a b c : A} → a ≐ b → b ≐ c → a ≐ c
  transitive≐ a≐b b≐c P Pa = b≐c P (a≐b P Pa)

  symmetric≐ : {a b : A} → a ≐ b → b ≐ a
  -- Set₁ != Set
--   symmetric≐ {a} {b} a≐b = a≐b (_≐ a) reflexive≐
  symmetric≐ {a} {b} a≐b P = a≐b (λ k → P k → P a) (reflexive≐ P)

open Leibniz

T : Set → Set₁
T A = ∀ (X : Set) → (A → X) → X

module WramUp (A : Set) where
  postulate
    paramT
      : (t : T A) → (X X′ : Set) (R : X → X′ → Set)
      → (k : A → X) (k′ : A → X′) (kR : (a : A) → R (k a) (k′ a))
      → R (t X k) (t X′ k′)

  i : A → T A
  i a X k = k a

  id : A → A
  id a = a

  j : T A → A
  j t = t A id

  ji : (a : A) → (j (i a) ≡ a)
  ji _ = refl

  ijext : (t : T A) (X : Set) (k : A → X) → (i (j t) X k ≡ t X k)
  ijext t X k = {!   !}


