module Dybjer where

module Bool where
  data Bool : Set where
    true : Bool
    false : Bool

  not : Bool → Bool
  not true = false
  not false = true

  if_then_else_ : Bool → Bool → Bool → Bool
  if true  then y else _ = y
  if false then _ else z = z

  _&&_ : Bool → Bool → Bool
  true && c = c
  false && _ = false

  infixl 50 _&&_

  _||_ : Bool → Bool → Bool
  true || _ = true
  false || c = c

  _=>_ : Bool → Bool → Bool
  true => c = c
  false => _ = true

  _<=>_ : Bool → Bool → Bool
  true <=> c = c
  false <=> c = not c

module Eq where
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

module Logic where
  data _&_ (A B : Set) : Set where
    <_,_> : A → B → A & B

  fst-& : {A B : Set} → A & B → A
  fst-& < x , _ > = x

  snd-& : {A B : Set} → A & B → B
  snd-& < _ , y > = y

  data _⋁_ (A B : Set) : Set where
    inl : A → A ⋁ B
    inr : B → A ⋁ B

  case : {A B C : Set} → (A → C) → (B → C) → A ⋁ B → C
  case f _ (inl x) = f x
  case _ g (inr x) = g x

  comm-⋁ : {A B : Set} → A ⋁ B → B ⋁ A
  comm-⋁ (inl x) = inr x
  comm-⋁ (inr x) = inl x

  comm-& : {A B : Set} → A & B → B & A
  comm-& (< x , y >) = < y , x >

  data ⊤ : Set where
    tt : ⊤

  data ⊥ : Set where

  nocase : {C : Set} → ⊥ → C
  nocase ()

  data _⊃_ (A B : Set) : Set where
    ⊃-intro : (A → B) → A ⊃ B

  mp : {A B : Set} → A ⊃ B → A → B
  mp (⊃-intro g) a = g a

  ¬ : Set → Set
  ¬ A = A → ⊥

  inverse-dn : {A : Set} → A → ¬ (¬ A)
  inverse-dn a = λ f → f a

  triple-negation : {A : Set} → ¬ (¬ (¬ A)) → ¬ A
  triple-negation f x = f (λ nx → nx x)

  em→dn : {A : Set} → (A ⋁ ¬ A) → ¬ (¬ A) → A
  em→dn (inl x)  _ = x
  em→dn (inr nx) f = nocase (f nx)

  em-irrefutable : {A : Set} → ¬ (¬ (A ⋁ ¬ A))
  em-irrefutable ¬em = ¬em (inr (λ x → ¬em (inl x)))

  dn→em : ((X : Set) → ¬ (¬ X) → X) → (A : Set) → (A ⋁ ¬ A)
  dn→em dn A = dn _ em-irrefutable

  data ∃ (A : Set) (P : A → Set) : Set where
    <_,_> : (a : A) → P a → ∃ A P

  witness : {A : Set} {P : A → Set} → ∃ A P → A
  witness < a , _ > = a

  proof : {A : Set} → {P : A → Set} → (c : ∃ A P) → P (witness c)
  proof < a , p > = p

  ∃-elim : {A : Set} → {P : A → Set} → {Q : Set} → ((a : A) → P a → Q) → ∃ A P → Q
  ∃-elim f < a , p > = f a p

  data ∀′ (A : Set) (P : A → Set) : Set where
    ∀′-intro : ((x : A) → P x) → ∀′ A P

  ∀′-elim : {A : Set} {P : A → Set} → ∀′ A P → (a : A) → P a
  ∀′-elim (∀′-intro f) a = f a

module Nat where
  open Bool
  open Eq
  open Logic

  data Nat : Set where
    zero : Nat
    succ : Nat → Nat

  iszero : Nat → Bool
  iszero zero = true
  iszero (succ n) = false

  one = succ zero
  two = succ one

  -- _+_ : Nat → Nat → Nat
  -- m + zero = m
  -- m + succ n = succ (m + n)
  _+_ : Nat → Nat → Nat
  zero + m = m
  succ n + m = succ (n + m)

  _+′_ : Nat → Nat → Nat
  m +′ zero = m
  m +′ succ n = succ (m +′ n)

  infixl 60 _+_

  _*_ : Nat → Nat → Nat
  zero * n = zero
  succ m * n = n + (m * n)

  infixl 70 _*_

  f : Nat → Nat → Nat → Nat
  f x y z = x + y + z

  {-# BUILTIN NATURAL Nat #-}
  {-# BUILTIN NATPLUS _+_ #-}
  {-# BUILTIN NATTIMES _*_ #-}

  _-_ : Nat → Nat → Nat
  zero - n = zero
  succ m - zero = succ m
  succ m - succ n = m - n

  _<_ : Nat → Nat → Bool
  zero < zero = false
  zero < succ n = true
  succ m < zero = false
  succ m < succ n = m < n

  ifn_then_else_ : Bool → Nat → Nat → Nat
  ifn true then y else _ = y
  ifn false then _ else z = z

  power : Nat → Nat → Nat
  power m zero = succ zero
  power m (succ n) = m * (power m n)

  factorial : Nat → Nat
  factorial zero = succ zero
  factorial (succ m) = succ m * factorial m

  -- _÷_ : Nat → Nat → Nat
  -- m ÷ n = error --ifn (iszero n || (m < n)) then zero else succ ((m - n) ÷ n)

  _==_ : Nat → Nat → Bool
  zero == zero = true
  zero == succ _ = false
  succ _ == zero = false
  succ m == succ n = m == n

  _==′_ : Nat → Nat → Bool
  m ==′ n = iszero (m - n) && iszero (n - m)

  _==″_ : Nat → Nat → Bool
  zero ==″ n with n
  ...           | zero = true
  ...           | succ _ = false
  succ m ==″ n with n
  ...             | zero = false
  ...             | succ n = m ==″ n

  -- associativity-plus : (m n p : Nat) → ((m + n) + p) ≡ (m + (n + p))
  -- associativity-plus m n zero = refl
  -- associativity-plus m n (succ p) = cong succ (associativity-plus m n p)
  associativity-plus : (m n p : Nat) → ((m + n) + p) ≡ (m + (n + p))
  associativity-plus zero n p = refl
  associativity-plus (succ m) n p = cong succ (associativity-plus m n p)

  natInd :
      {P : Nat → Set}
    → P zero
    → ((n : Nat) → P n → P (succ n))
    → (n : Nat)
    → P n
  natInd base _    zero     = base
  natInd base step (succ n) = step n (natInd base step n)

  -- Peano's axioms
  peano-3-axiom : {m n : Nat} → succ m ≡ succ n → m ≡ n
  peano-3-axiom refl = refl

  peano-3-axiom′ : {m n : Nat} → succ m ≡ succ n → m ≡ n
  peano-3-axiom′ {m} .{m} refl = refl

  -- The case for the constructor refl is impossible
  -- because unification ended with a conflicting equation
  --   zero ≟ succ n
  -- Possible solution: remove the clause, or use an absurd pattern ().
  -- when checking that the pattern refl has type zero ≡ succ n
  peano-4-axiom : {n : Nat} → zero ≡ succ n → ⊥
  peano-4-axiom ()

  subst→peano-3-axiom : {m n : Nat} → succ m ≡ succ n → m ≡ n
  subst→peano-3-axiom {m} {_} p = subst {P = λ k → pred (succ m) ≡ pred k} p refl
    where
      pred : Nat → Nat
      pred zero = zero
      pred (succ n) = n

  subst→peano-4-axiom : {n : Nat} → zero ≡ succ n → ⊥
  subst→peano-4-axiom p = subst {P = case′} p tt
    where
      case′ : Nat → Set
      case′ zero     = ⊤
      case′ (succ _) = ⊥


  associativity-plus-ind : (m n p : Nat) → ((m + n) + p) ≡ (m + (n + p))
  associativity-plus-ind m n p =
    natInd {λ m → ((m + n) + p) ≡ (m + (n + p))}
      refl
      (λ n r → cong succ r)
      m

id : (X : Set) → X → X
id X x = x

id′ : (X : Set) → X → X
id′ = λ X x → x

id-implicit : {X : Set} → X → X
id-implicit x = x

id-implicit′ : {X : Set} → X → X
id-implicit′ = λ x → x

_◦_ : {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
(g ◦ f) x = g (f x)

K : {X Y : Set} → X → Y → X
K x _ = x

S : {X Y Z : Set} → (X → Y → Z) → (X -> Y) → X → Z
S f g x = f x (g x)

open Bool
open Eq
open Nat
open Logic

data _×_ (A B : Set) : Set where
  <_,_> : A → B → A × B

fst : {A B : Set} → A × B → A
fst < a , _ > = a

snd : {A B : Set} → A × B → B
snd < _ , b > = b

×-inj : {A B : Set} → (p1 p2 : A × B) → p1 ≡ p2 → (fst p1 ≡ fst p2) & (snd p1 ≡ snd p2)
×-inj (< x , x₁ >) .(< x , x₁ >) refl = < refl , refl >

×-inj′ : {A B : Set} → (p1 p2 : A × B) → p1 ≡ p2 → (fst p1 ≡ fst p2) & (snd p1 ≡ snd p2)
×-inj′ p1 p2 p = subst {P = λ p → (fst p1 ≡ fst p) & (snd p1 ≡ snd p)} p < refl , refl >

×-inj″ : {A B : Set} → (p1 p2 : A × B) → p1 ≡ p2 → (fst p1 ≡ fst p2) & (snd p1 ≡ snd p2)
×-inj″ _ _ refl = < refl , refl >

record _×′_ (A B : Set) : Set where
  constructor <_,_>′
  field
    l1 : A
    l2 : B

open _×′_

×′-inj : {A B : Set} → (p1 p2 : A ×′ B) → p1 ≡ p2 → (l1 p1 ≡ l1 p2) & (l2 p1 ≡ l2 p2)
×′-inj (< x , x₁ >′) .(< x , x₁ >′) refl = < refl , refl >

×′-inj′ : {A B : Set} → (p1 p2 : A ×′ B) → p1 ≡ p2 → (l1 p1 ≡ l1 p2) & (l2 p1 ≡ l2 p2)
×′-inj′ p1 p2 p = subst {P = λ p → (l1 p1 ≡ l1 p) & (l2 p1 ≡ l2 p)} p < refl , refl >

×′-inj″ : {A B : Set} → (p1 p2 : A ×′ B) → p1 ≡ p2 → (l1 p1 ≡ l1 p2) & (l2 p1 ≡ l2 p2)
×′-inj″ _ _ refl = < refl , refl >

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f < x , y > = f x y
