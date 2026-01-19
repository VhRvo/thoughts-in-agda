{-# OPTIONS --safe #-}
module ListMaxZ where

open import Data.Integer
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

open import Preloaded

open import Data.Nat using (ℕ) renaming (_⊔_ to _ℕ⊔_; _⊓_ to _ℕ⊓_; _≤_ to _ℕ≤_)
open import Data.List.Relation.Unary.Any as Any
  using (Any; here; there)

caseℕ⊔ : (m n : ℕ) → m ℕ⊔ n ≡ m ⊎ m ℕ⊔ n ≡ n
caseℕ⊔ ℕ.zero n = inj₂ refl
caseℕ⊔ (ℕ.suc m) ℕ.zero = inj₁ refl
caseℕ⊔ (ℕ.suc m) (ℕ.suc n) =
  Data.Sum.map (cong ℕ.suc) (cong ℕ.suc) (caseℕ⊔ m n)

caseℕ⊓ : (m n : ℕ) → m ℕ⊓ n ≡ m ⊎ m ℕ⊓ n ≡ n
caseℕ⊓ ℕ.zero n = inj₁ refl
caseℕ⊓ (ℕ.suc m) ℕ.zero = inj₂ refl
caseℕ⊓ (ℕ.suc m) (ℕ.suc n) =
  Data.Sum.map (cong ℕ.suc) (cong ℕ.suc) (caseℕ⊓ m n)

caseℤ⊔ : (m n : ℤ) → m ⊔ n ≡ m ⊎ m ⊔ n ≡ n
caseℤ⊔ (+ m )   (+ n) =
  Data.Sum.map (cong (+_)) (cong (+_)) (caseℕ⊔ m n)
caseℤ⊔ (+ m )   -[1+ n ] = inj₁ refl
caseℤ⊔ -[1+ m ] (+ n)    = inj₂ refl
caseℤ⊔ -[1+ m ] -[1+ n ] =
  Data.Sum.map (cong -[1+_]) (cong -[1+_]) (caseℕ⊓ m n)

ℕ≤-refl : (m : ℕ) → m ℕ≤ m
ℕ≤-refl ℕ.zero    = _ℕ≤_.z≤n
ℕ≤-refl (ℕ.suc m) = _ℕ≤_.s≤s (ℕ≤-refl m)

mℕ≤mℕ⊔n : (m n : ℕ) → m ℕ≤ m ℕ⊔ n
mℕ≤mℕ⊔n ℕ.zero    _         = _ℕ≤_.z≤n
mℕ≤mℕ⊔n (ℕ.suc m) ℕ.zero    = _ℕ≤_.s≤s (ℕ≤-refl m)
mℕ≤mℕ⊔n (ℕ.suc m) (ℕ.suc n) = _ℕ≤_.s≤s (mℕ≤mℕ⊔n m n)

mℕ⊓nℕ≤m : (m n : ℕ) → m ℕ⊓ n ℕ≤ m
mℕ⊓nℕ≤m ℕ.zero    n         = _ℕ≤_.z≤n
mℕ⊓nℕ≤m (ℕ.suc m) ℕ.zero    = _ℕ≤_.z≤n
mℕ⊓nℕ≤m (ℕ.suc m) (ℕ.suc n) = _ℕ≤_.s≤s (mℕ⊓nℕ≤m m n)

m≤m⊔n : (m n : ℤ) → m ≤ m ⊔ n
m≤m⊔n (+ m) (+ n)       = +≤+ (mℕ≤mℕ⊔n m n)
m≤m⊔n (+ m) -[1+ _ ]    = +≤+ (ℕ≤-refl m)
m≤m⊔n -[1+ _ ] (+ _)    = -≤+
m≤m⊔n -[1+ m ] -[1+ n ] = -≤- (mℕ⊓nℕ≤m m n)

nℕ≤l→mℕ⊓nℕ≤l : {n l : ℕ} → (m : ℕ) → n ℕ≤ l → m ℕ⊓ n ℕ≤ l
nℕ≤l→mℕ⊓nℕ≤l ℕ.zero    nℕ≤l            = _ℕ≤_.z≤n
nℕ≤l→mℕ⊓nℕ≤l (ℕ.suc m) _ℕ≤_.z≤n        = _ℕ≤_.z≤n
nℕ≤l→mℕ⊓nℕ≤l (ℕ.suc m) (_ℕ≤_.s≤s nℕ≤l) = _ℕ≤_.s≤s (nℕ≤l→mℕ⊓nℕ≤l m nℕ≤l)

lℕ≤n→lℕ≤mℕ⊔n : {l n : ℕ} → (m : ℕ) → l ℕ≤ n → l ℕ≤ m ℕ⊔ n
lℕ≤n→lℕ≤mℕ⊔n ℕ.zero _ℕ≤_.z≤n = _ℕ≤_.z≤n
lℕ≤n→lℕ≤mℕ⊔n ℕ.zero (_ℕ≤_.s≤s lℕ≤n) = _ℕ≤_.s≤s lℕ≤n
lℕ≤n→lℕ≤mℕ⊔n (ℕ.suc m) _ℕ≤_.z≤n = _ℕ≤_.z≤n
lℕ≤n→lℕ≤mℕ⊔n (ℕ.suc m) (_ℕ≤_.s≤s lℕ≤n) = _ℕ≤_.s≤s (lℕ≤n→lℕ≤mℕ⊔n m lℕ≤n)

mℕ⊔n≡nℕ⊔m : ∀ m n → m ℕ⊔ n ≡ n ℕ⊔ m
mℕ⊔n≡nℕ⊔m ℕ.zero ℕ.zero       = refl
mℕ⊔n≡nℕ⊔m ℕ.zero (ℕ.suc n)    = refl
mℕ⊔n≡nℕ⊔m (ℕ.suc m) ℕ.zero    = refl
mℕ⊔n≡nℕ⊔m (ℕ.suc m) (ℕ.suc n) = cong ℕ.suc (mℕ⊔n≡nℕ⊔m m n)

mℕ⊓n≡nℕ⊓m : ∀ m n → m ℕ⊓ n ≡ n ℕ⊓ m
mℕ⊓n≡nℕ⊓m ℕ.zero ℕ.zero       = refl
mℕ⊓n≡nℕ⊓m ℕ.zero (ℕ.suc n)    = refl
mℕ⊓n≡nℕ⊓m (ℕ.suc m) ℕ.zero    = refl
mℕ⊓n≡nℕ⊓m (ℕ.suc m) (ℕ.suc n) = cong ℕ.suc (mℕ⊓n≡nℕ⊓m  m n)

m⊔n≡n⊔m : ∀ m n → m ⊔ n ≡ n ⊔ m
m⊔n≡n⊔m (+ m) (+ n) = cong +_ (mℕ⊔n≡nℕ⊔m m n)
m⊔n≡n⊔m (+ m) -[1+ n ] = refl
m⊔n≡n⊔m (-[1+_] m) (+ n) = refl
m⊔n≡n⊔m (-[1+_] m) -[1+ n ] = cong -[1+_] (mℕ⊓n≡nℕ⊓m m n)

l≤n→l≤m⊔n : {l n : ℤ} → (m : ℤ) → l ≤ n → l ≤ m ⊔ n
l≤n→l≤m⊔n (+ _)    (-≤- _)    = -≤+
l≤n→l≤m⊔n -[1+ m ] (-≤- lℕ≤n) = -≤- (nℕ≤l→mℕ⊓nℕ≤l m lℕ≤n)
l≤n→l≤m⊔n (+ _)    -≤+        = -≤+
l≤n→l≤m⊔n -[1+ m ] -≤+        = -≤+
l≤n→l≤m⊔n (+ m)    (+≤+ lℕ≤n) = +≤+ (lℕ≤n→lℕ≤mℕ⊔n m lℕ≤n)
l≤n→l≤m⊔n -[1+ m ] (+≤+ lℕ≤n) = +≤+ lℕ≤n

m∈xs→x⊔m∈x∷xs : ∀ {m x xs} → m ∈ xs → x ⊔ m ∈ x ∷ xs
m∈xs→x⊔m∈x∷xs {m} {x} {xs} m∈xs
  with caseℤ⊔ x m
  -- compiler: I'm not sure if there should be a case for the constructor refl
...  | inj₁ ≡x = subst (λ hole → x ⊔ m ∈ hole ∷ xs) ≡x (here refl)
...  | inj₂ ≡m = there (subst (λ hole → hole ∈ xs) (sym ≡m) m∈xs)

x⊔+0∈x∷xs⊎x⊔+0≡+0 : ∀ {x xs} → x ⊔ + 0 ∈ x ∷ xs ⊎ x ⊔ + 0 ≡ + 0
x⊔+0∈x∷xs⊎x⊔+0≡+0 {x} {xs}
  with caseℤ⊔ x (+ 0)
...  | inj₁ ≡x  = inj₁ (subst (λ hole → x ⊔ (+ 0) ∈ hole ∷ xs) ≡x (here refl))
...  | inj₂ ≡+0 = inj₂ ≡+0

list-max-ℤ-spec : ∀ (l : List ℤ) → let m = list-max-ℤ l in
                    (∀ x → x ∈ l → x ≤ m) × (m ∈ l ⊎ m ≡ + 0)
list-max-ℤ-spec [] = (λ _ ()) , inj₂ refl
list-max-ℤ-spec (x ∷ xs)
  with list-max-ℤ xs | list-max-ℤ-spec xs
...  | m             | ind , inj₁ m∈xs = (λ{.(x) (here refl)  → m≤m⊔n x m
                                          ; y    (there y∈xs) → l≤n→l≤m⊔n x (ind y y∈xs)}) , inj₁ (m∈xs→x⊔m∈x∷xs m∈xs)
...  | .(+ 0)         | ind , inj₂ refl = (λ{.(x) (here refl)  → m≤m⊔n x (+ 0)
                                          ; y    (there y∈xs) → l≤n→l≤m⊔n x (ind y y∈xs)}) , x⊔+0∈x∷xs⊎x⊔+0≡+0