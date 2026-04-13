{-# OPTIONS --without-K #-}

module Miscellaneous.Nat-UIP-FromScratch where

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

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

suc-inj : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

-- 把 with 体提取为独立函数，使得证明可以用 cong 代替 with/rewrite
suc-dec : ∀ {m n : Nat} → Dec (m ≡ n) → Dec (suc m ≡ suc n)
suc-dec (yes p) = yes (cong suc p)
suc-dec (no np) = no (λ q → np (suc-inj q))

_≟_ : (m n : Nat) → Dec (m ≡ n)
zero  ≟ zero  = yes refl
zero  ≟ suc n = no (λ ())
suc m ≟ zero  = no (λ ())
suc m ≟ suc n = suc-dec (m ≟ n)

pick : ∀ {m n : Nat} → (m ≡ n) → Dec (m ≡ n) → (m ≡ n)
pick p (yes q) = q
pick p (no np) = ⊥-elim (np p)

canon : ∀ {m n : Nat} → (m ≡ n) → (m ≡ n)
canon {m} {n} p = pick p (m ≟ n)

pick-const : ∀ {m n : Nat} (p q : m ≡ n) (d : Dec (m ≡ n)) → pick p d ≡ pick q d
pick-const p q (yes r) = refl
pick-const p q (no np) = ⊥-elim (np p)

canon-const : ∀ {m n : Nat} (p q : m ≡ n) → canon p ≡ canon q
canon-const {m} {n} p q = pick-const p q (m ≟ n)

-- 关键：suc m ≟ suc m = suc-dec (m ≟ m)，所以 cong suc-dec (refl≟ m) 即可
refl≟ : (m : Nat) → (m ≟ m) ≡ yes refl
refl≟ zero    = refl
refl≟ (suc m) = cong suc-dec (refl≟ m)

-- canon refl = pick refl (m ≟ m)，用 cong (pick refl) (refl≟ m) 即可
canon-refl : (m : Nat) → canon {m} {m} refl ≡ refl
canon-refl m = cong (pick refl) (refl≟ m)

refl≡canon : ∀ (m : Nat) → refl ≡ canon {m} {m} refl
refl≡canon m = sym (canon-refl m)

-- J（等式归纳），只用 builtin equality 的模式匹配即可
J : ∀ {A : Set} {x : A}
    (P : {y : A} → x ≡ y → Set) →
    P refl →
    {y : A} (p : x ≡ y) → P p
J P pr refl = pr

-- 现在可以证明 p ≡ canon p（基例用 canon-refl m，而不是硬写 refl）
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
