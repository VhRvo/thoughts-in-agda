module IgnoringDotPattern where

open import Data.Nat using (ℕ; zero; suc)

data Image_∋_ {A B : Set} (f : A → B) : B → Set where
    im : (x : A) → Image f ∋ f x

inv : {A B : Set} (f : A → B) (y : B) → Image f ∋ y → A
inv f .(f x) (im x) = x

data _==_ {A : Set} (x : A) : A → Set where
    refl : x == x

data _≠_ : ℕ → ℕ → Set where
    z≠s : {n : ℕ} →  zero ≠ suc n
    s≠z : {n : ℕ} →  suc n ≠ zero
    s≠s : {n m : ℕ} → n ≠ m → suc n ≠ suc m

data Equal? (n m : ℕ) : Set where
    eq : n == m → Equal? n m
    neq : n ≠ m → Equal? n m

equal? : (n m : ℕ) → Equal? n m
equal? zero zero = eq refl
equal? zero (suc m) = neq z≠s
equal? (suc n) zero = neq s≠z
equal? (suc n) (suc m) with equal? n m
... |  eq refl = eq refl
... |  neq n≠m = neq (s≠s n≠m)


