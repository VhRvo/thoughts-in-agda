{-# OPTIONS --safe #-}
module NatEqBool where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product
open import Relation.Nullary

card≥3 : Set → Set
card≥3 A = Σ A (λ x → ∃[ y ] ∃[ z ] (x ≢ y × y ≢ z × x ≢ z))
-- card≥3 A = Σ[ x ∈ A ] ∃[ y ] ∃[ z ] (x ≢ y × y ≢ z × x ≢ z)

card≥3[ℕ] : card≥3 ℕ
card≥3[ℕ] = 0 , 1 , 2 , ((λ ()) , (λ ()) , (λ ()))

¬card3[Bool] : ¬ (card≥3 Bool)
¬card3[Bool] (true  , true  , _     , (neq , _   , _))    =  neq refl
¬card3[Bool] (false , false , _     , (neq , _   , _))    =  neq refl
¬card3[Bool] (true  , _     , true  , (_   , _   , neq))  =  neq refl
¬card3[Bool] (false , _     , false , (_   , _   , neq))  =  neq refl
¬card3[Bool] (_     , true  , true  , (_   , neq , _))    =  neq refl
¬card3[Bool] (_     , false , false , (_   , neq , _))    =  neq refl

is-ℕ-Bool : ℕ ≡ Bool ⊎ ℕ ≢ Bool
is-ℕ-Bool = inj₂ (λ eq → ¬card3[Bool] (subst card≥3 eq card≥3[ℕ]))
