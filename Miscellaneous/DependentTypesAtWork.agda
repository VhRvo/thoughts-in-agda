module DependentTypesAtWork where

open import Dybjer
open Logic
open Nat

module RecursiveFamily where

  Vec : Set → Nat → Set
  Vec A zero = ⊤
  Vec A (succ n) = A × Vec A n

  zip : {A B : Set} → (n : Nat)
    → Vec A n → Vec B n → Vec (A × B) n
  zip zero tt tt = tt
  zip (succ n) < a , as > < b , bs > = < < a , b > , zip n as bs >

  head : {A : Set} → {n : Nat} → Vec A (succ n) → A
  head < a , _ > = a

  tail : {A : Set} → {n : Nat} → Vec A (succ n) → Vec A n
  tail < _ , as > = as

  map : {A B : Set} → (A → B) → (n : Nat) → Vec A n → Vec B n
  map f zero     tt         = tt
  map f (succ n) < a , as > = < f a , map f n as >

--   map′ : {A B : Set} → (A → B) → (n : Nat) → Vec A n → Vec B n
--   map′ f .zero     tt         = tt
--   map′ f .(succ n) < a , as > = < f a , map′ f n as >

  Fin : Nat → Set
  Fin zero = ⊥
  Fin (succ n) = ⊤ ⋁ Fin n

  Fin-0-count : Fin zero → Nat
  Fin-0-count ()

  Fin-1-count : Fin (succ zero) → Nat
  Fin-1-count (inl tt) = 1
  Fin-1-count (inr ())

  Fin-2-count : Fin (succ (succ zero)) → Nat
  Fin-2-count (inl tt) = 1
  Fin-2-count (inr (inl tt)) = 2
  Fin-2-count (inr (inr ()))

module InductiveFamily where
  data Vec (A : Set) : Nat → Set where
    [] : Vec A zero
    _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)

  zip : {A B : Set} → (n : Nat) → Vec A n → Vec B n → Vec (A × B) n
  zip zero [] [] = []
  zip (succ n) (x :: xs) (y :: ys) = < x , y > :: zip n xs ys

  zip′ : {A B : Set} → (n : Nat) → Vec A n → Vec B n → Vec (A × B) n
  zip′ zero     []        []        = []
  zip′ (succ n) (x :: xs) (y :: ys) = < x , y > :: zip′ n xs ys

  head : {A : Set} {n : Nat} → Vec A (succ n) → A
  head (x :: _) = x

  tail : {A : Set} {n : Nat} → Vec A (succ n) → Vec A n
  tail (_ :: xs) = xs

  map : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
  map f []        = []
  map f (x :: xs) = f x :: map f xs

  data Fin : Nat → Set where
    fzero : {n : Nat} → Fin (succ n)
    fsucc : {n : Nat} → Fin n → Fin (succ n)

  _!_ : {A : Set} {n : Nat} → Vec A n → Fin n → A
  [] ! ()
  (x :: _)  ! fzero = x
  (_ :: xs) ! fsucc i = xs ! i

  _!!_ : {A : Set} {n : Nat} → Vec A (succ n) → Fin (succ n) → A
  (x :: _)  !! fzero = x
  (_ :: xs) !! fsucc i = xs ! i

  data DBTree (A : Set) : Nat → Set where
    dlf : A → DBTree A zero
    dnd : {n : Nat} → DBTree A n → DBTree A n → DBTree A (succ n)

  data BTree (A : Set) : Nat → Set where
    dlf : A → BTree A zero
    dnd1 : {n : Nat} → BTree A n → BTree A n → BTree A (succ n)
    dnd2 : {n : Nat} → BTree A n → BTree A (succ n) → BTree A (succ (succ n))
    dnd3 : {n : Nat} → BTree A (succ n) → BTree A n → BTree A (succ (succ n))

  data Term (n : Nat) : Set where
    var : Fin n → Term n
    lam : Term n → Term n
    app : Term n → Term n → Term n

--   _==>_ : (A B : Set) → Set
--   A ==> B = A → B
  data _==>_ (A B : Set) : Set where
    fun : (A → B) → A ==> B

  apply : {A B : Set} → A ==> B → A → B
  apply (fun f) a = f a

  apply′ : {A B : Set} → A ==> B → A → B
  apply′ (fun f) = f

  _<==>_ : Set → Set → Set
  A <==> B = (A ==> B) & (B ==> A)

--   Forall : (A : Set) → (B : A → Set) → Set
--   Forall A B = (x : A) → B x
  data Forall (A : Set) (B : A → Set) : Set where
    dfun : ((x : A) → B x) → Forall A B

  dapply : {A : Set} {B : A → Set} → Forall A B → (x : A) → B x
  dapply (dfun f) x = f x

  data Exists (A : Set) (B : A → Set) : Set where
    [_,_] : (a : A) → B a → Exists A B

  dfst : {A : Set} {B : A → Set} → Exists A B → A
  dfst [ a , _ ] = a

  dsnd : {A : Set} {B : A → Set} → (p : Exists A B) → B (dfst p)
  dsnd [ _ , b ] = b

  dcase : {A B : Set} → {C : A ⋁ B → Set} → (z : A ⋁ B)
    → ((x : A) → C (inl x)) → ((y : B) → C (inr y)) → C z
  dcase (inl x) f _ = f x
  dcase (inr y) _ g = g y

  dnocase : {A : ⊥ → Set} → (z : ⊥) → A z
  dnocase ()

  data _≡_ {A : Set} : A → A → Set where
    refl : (a : A) → a ≡ a

  subst : {A : Set} → {C : A → Set}
    → {a′ a″ : A} → a′ ≡ a″ → C a′ → C a″
  subst (refl a) c = c

  natrec : {C : Nat → Set} → (C zero) → ((n : Nat) → C n → C (succ n)) → (n : Nat) → C n
  natrec base _    zero     = base
  natrec base step (succ n) = step n (natrec base step n)

  plus : Nat → Nat → Nat
  plus n m = natrec m (λ x r → succ r) n

  mult : Nat → Nat → Nat
  mult n m = natrec zero (λ x r → plus m r) n

  eq-succ : {n m : Nat} → n ≡ m → succ n ≡ succ m
  eq-succ (refl a) = refl (succ a)

  eq-zero : (m : Nat) → (zero +′ m) ≡ m
  eq-zero zero = refl zero
  eq-zero (succ m) = eq-succ (eq-zero m)

  eq-succ+ : (n m : Nat) → (succ n +′ m) ≡ succ (n +′ m)
  eq-succ+ n zero = refl (succ n)
  eq-succ+ n (succ m) = eq-succ (eq-succ+ n m)

  eq-succ′ : {n m : Nat} → n ≡ m → succ n ≡ succ m
  eq-succ′ {n} eq = subst {C = λ k → succ n ≡ succ k} eq (refl (succ n))

  eq-plus-rec : (n m : Nat) → n + m ≡ plus n m
  eq-plus-rec n m = natrec (refl m) (λ n' ih → eq-succ {n' + m} {plus n' m} ih) n

  substEq : {A : Set} → (m : Nat) → (zero +′ m) ≡ m → Vec A m → Vec A (zero +′ m)
  substEq {A} m eq = subst {C = λ k → Vec A k → Vec A (zero +′ m)} eq (λ x → x)

  _++′_ : {A : Set} {n m : Nat} → Vec A n → Vec A m → Vec A (n +′ m)
  _++′_ {_} {_} {m} [] ys = substEq m (eq-zero m) ys
  _++′_ {_} {_} {m} (x :: xs) ys = {!   !}

module BTree where
  open Eq using (_≡_)
  postulate
    A : Set
    _<=_ : A → A → Set
    total : (a b : A) → (a <= b) ⋁ (b <= a)
    anti-sym : {a b : A} → a <= b → b <= a → a ≡ b
    refl : (a : A) → a <= a
    trans : {a b c : A} → a <= b → b <= c → a <= c

  data BTree : Set where
    lf : BTree
    nd : A → BTree → BTree → BTree

  all-leq : BTree → A → Set
  all-leq lf a = ⊤
  all-leq (nd x l r) a = ((x <= a) & all-leq l a) & all-leq r a

  all-geq : BTree → A → Set
  all-geq lf a = ⊤
  all-geq (nd x l r) a = ((a <= x) & all-geq l a) & all-geq r a

  Sorted : BTree → Set
  Sorted lf = ⊤
  Sorted (nd a l r) = (all-geq l a & Sorted l) & (all-leq r a & Sorted r)

