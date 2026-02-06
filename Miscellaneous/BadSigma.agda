module BadSigma where

data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

transport
 : {A : Set}
 → {P : A → Set}
 → {x y : A}
 → (eq : x ≡ y)
 → P x → P y
transport refl px = px

data Sigma (Index : Set) (F : Index → Set) : Set where
    sigma : (i : Index) → (F i) → Sigma Index F

Sigma-elim
 : {Index : Set}
 → {F : Index → Set}
 → {Motive : Sigma Index F → Set}
 → (p : (i : Index) → (e : F i) → Motive (sigma i e))
 → (it : Sigma Index F) → Motive it
Sigma-elim p (sigma i e) = p i e

from
 : {Index : Set}
 → {F : Index → Set}
 → {i j : Index}
 → {x : F i}
 → {y : F j}
 → (sigma i x ≡ sigma j y)
 → Sigma (i ≡ j) (λ q → transport q x ≡ y)
from refl = sigma refl refl

to
 : {Index : Set}
 → {F : Index → Set}
 → {i j : Index}
 → {x : F i}
 → {y : F j}
 → Sigma (i ≡ j) (λ q → transport q x ≡ y)
 → (sigma i x ≡ sigma j y)
to (sigma fste snde) = {!   !}

-- from∘to
--  : {Index : Set}
--  → {F : Index → Set}
--  → {i j : Index}
--  → {x : F i}
--  → {y : F j}
--  → (eq : Sigma (i ≡ j) (λ q → transport q x ≡ y))
--  → from (to eq) ≡ eq
-- from∘to (sigma refl refl) = refl

-- to∘from
--  : {Index : Set}
--  → {F : Index → Set}
--  → {i j : Index}
--  → {x : F i}
--  → {y : F j}
--  → (eq : sigma i x ≡ sigma j y)
--  → to (from eq) ≡ eq
-- to∘from refl = refl
