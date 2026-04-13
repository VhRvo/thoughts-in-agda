{-# OPTIONS --without-K #-}

module Nat-UIP-FromScratch-NoRewrite where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

data ⊥ : Set where
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

¬_ : Set → Set
¬ P = P → ⊥

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : (¬ P) → Dec P

-- equality combinators
sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- J / subst (no rewrite)
J : ∀ {A : Set} {x : A}
    (P : {y : A} → x ≡ y → Set) →
    P refl →
    {y : A} (p : x ≡ y) → P p
J P pr refl = pr

subst : ∀ {A : Set} {x y : A} → x ≡ y → (P : A → Set) → P x → P y
subst refl P px = px

-- suc injective
suc-inj : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

-- transport decidability across suc, definitional (no with)
sucDec : ∀ {m n : Nat} → Dec (m ≡ n) → Dec (suc m ≡ suc n)
sucDec (yes p) = yes (cong suc p)
sucDec (no np) = no (λ q → np (suc-inj q))

-- Nat decidable equality, no with, so suc-case is definitional sucDec (m≟n)
_≟_ : (m n : Nat) → Dec (m ≡ n)
zero   ≟ zero    = yes refl
zero   ≟ suc n   = no (λ ())
suc m  ≟ zero    = no (λ ())
suc m  ≟ suc n   = sucDec (m ≟ n)

-- canon' parameterized by the Dec evidence
canon′ : ∀ {m n : Nat} → Dec (m ≡ n) → (m ≡ n) → (m ≡ n)
canon′ (yes q) _ = q
canon′ (no np) p = ⊥-elim (np p)

canon : ∀ {m n : Nat} → (m ≡ n) → (m ≡ n)
canon {m} {n} p = canon′ (m ≟ n) p

canon-const : ∀ {m n : Nat} (p q : m ≡ n) → canon p ≡ canon q
canon-const {m} {n} p q with m ≟ n
... | yes r = refl
... | no np = ⊥-elim (np p)

-- decidable equality reflexivity computes to yes refl (now easy: cong sucDec)
refl≟ : (m : Nat) → (m ≟ m) ≡ yes refl
refl≟ zero    = refl
refl≟ (suc m) = cong sucDec (refl≟ m)

-- canon refl = refl, proven via subst (no rewrite)
canon-refl : (m : Nat) → canon {m} {m} refl ≡ refl
canon-refl m =
  subst (sym (refl≟ m)) P base
  where
    P : Dec (m ≡ m) → Set
    P d = canon′ d refl ≡ refl
    base : P (yes refl)
    base = refl

-- p ≡ canon p via J, base uses canon-refl (not definitional reduction)
p≡canon : ∀ {m n : Nat} (p : m ≡ n) → p ≡ canon p
p≡canon {m} p =
  J {A = Nat} {x = m}
    (λ {y} p → p ≡ canon p)
    (sym (canon-refl m))
    p

uipNat : ∀ {m n : Nat} (p q : m ≡ n) → p ≡ q
uipNat p q =
  trans (p≡canon p)
        (trans (canon-const p q)
               (sym (p≡canon q)))

one : Nat
one = suc zero

uip1 : (p : one ≡ one) → p ≡ refl
uip1 p = uipNat p refl
