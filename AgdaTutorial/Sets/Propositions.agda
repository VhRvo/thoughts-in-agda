module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt

⊤×⊥ : ⊤ × ⊥ → ⊥
⊤×⊥ (tt , ())

⊥×⊥ : ⊥ × ⊥ → ⊥
⊥×⊥ (() , ())

⊤⊎⊤ : ⊤ ⊎ ⊤
⊤⊎⊤ = inj₁ tt

⊤⊎⊥ : ⊤ ⊎ ⊥
⊤⊎⊥ = inj₁ tt

⊥⊎⊥ : ⊥ ⊎ ⊥ → ⊥
⊥⊎⊥ (inj₁ ())
⊥⊎⊥ (inj₂ ())

proof : ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤
proof = inj₂ (inj₁ tt)

data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m : ℕ} → {n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

3≤7 : 3 ≤ 7
3≤7 = s≤s (s≤s (s≤s z≤n))

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))

4≰2 : 4 ≤ 2 → ⊥
4≰2 (s≤s (s≤s ()))

8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s x) = 7≰3 x

module IsDoubleOf where
    open import Agda.Builtin.Equality
    data _isDoubleOf_ : ℕ → ℕ → Set where
        base : 0 isDoubleOf 0
        step : {m : ℕ} → {n : ℕ} → m isDoubleOf n → (suc (suc m)) isDoubleOf (suc n)

    8isDoubleOf4 : 8 isDoubleOf 4
    8isDoubleOf4 = step (step (step (step base)))

    9isNotDoubleOf4 : 9 isDoubleOf 4 → ⊥
    9isNotDoubleOf4 (step (step (step (step ()))))

    1isNotDoubleOf0 : 1 isDoubleOf 0 → ⊥
    1isNotDoubleOf0 ()

    ind :
        (Motive : ℕ → ℕ → Set) →
        (baseCase : Motive 0 0) →
        (stepCase : {m n : ℕ} → Motive m n → Motive (suc (suc m)) (suc n)) →
        {m n : ℕ} →
        m isDoubleOf n →
        Motive m n
    ind Motive baseCase stepCase base = baseCase
    ind Motive baseCase stepCase (step x) = stepCase (ind Motive baseCase stepCase x)

    1isNotDoubleOf0′ : 1 isDoubleOf 0 → ⊥
    1isNotDoubleOf0′ proof = ind (\m n → (m ≡ 1 × n ≡ 0) → ⊥) baseCase  stepCase proof ( refl , refl )
        where
            baseCase : (0 ≡ 1 × 0 ≡ 0) → ⊥
            baseCase (() , _)

            stepCase : {m n : ℕ} → ((m ≡ 1) × (n ≡ 0) → ⊥) → ((suc (suc m)) ≡ 1 × (suc n) ≡ 0) → ⊥
            stepCase ih (() , ())

module Single where
    data Odd : ℕ → Set where
        base : Odd 1
        step : {n : ℕ} → Odd n → Odd (suc (suc n))

    Odd9 : Odd 9
    Odd9 = step (step (step (step base)))

    ¬Odd8 : Odd 8 → ⊥
    ¬Odd8 (step (step (step (step ()))))

module Mutual where
    data Even : ℕ → Set
    data Odd : ℕ → Set

    data Even where
        base : Even zero
        step : {n : ℕ} → Odd n → Even (suc n)

    data Odd where
        step : {n : ℕ} → Even n → Odd (suc n)

data _≡_ : ℕ → ℕ → Set where
    base : 0 ≡ 0
    step : {m : ℕ} → {n : ℕ} → m ≡ n → suc m ≡ suc n

data _≢_ : ℕ → ℕ → Set where
    base1 : {n : ℕ} → suc n ≢ zero
    base2 : {n : ℕ} → zero ≢ suc n
    step : {m n : ℕ} → m ≢ n → suc m ≢ suc n
