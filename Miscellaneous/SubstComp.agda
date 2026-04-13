{-# OPTIONS --without-K #-}

{-
  Calculating the Composition of Substitution — Agda proof
  =========================================================

  Original derivation (Haskell):
    https://gist.github.com/VhRvo/03707118998ae937de189bb1e849802e

  We prove:
    subst (comp s1 s2) t ≡ subst s1 (subst s2 t)

  where:
    subst σ (Variable s)     = fromMaybe (Variable s) (σ s)
    subst σ (Predicate s ts) = Predicate s (substList σ ts)
    comp  s1 s2 k            = Maybe.map (subst s1) (s2 k) <|> s1 k

  Key insight: represent Substitution as a *function* Symbol → Maybe Term.
  This makes "Axiom 2" (naturality of lookup w.r.t. fmap) trivially true by
  definition, so only two fromMaybe lemmas are needed.
-}

module Miscellaneous.SubstComp where

open import Data.String    using (String)
open import Data.Maybe     using (Maybe; just; nothing; fromMaybe)
import      Data.Maybe  as Maybe
open import Data.List      using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

-- ─── Types ───────────────────────────────────────────────────────────────────

Symbol : Set
Symbol = String

-- Terms are defined mutually with List Term (embedded via the Predicate constructor)
data Term : Set where
  Variable  : Symbol      → Term
  Predicate : Symbol → List Term → Term

-- Substitution as a pure function — no finite map library needed
Substitution : Set
Substitution = Symbol → Maybe Term

-- ─── Operations ──────────────────────────────────────────────────────────────

-- Mutual recursion handles the List Term embedded inside Predicate
mutual
  subst : Substitution → Term → Term
  subst σ (Variable s)     = fromMaybe (Variable s) (σ s)
  subst σ (Predicate s ts) = Predicate s (substList σ ts)

  substList : Substitution → List Term → List Term
  substList σ []       = []
  substList σ (t ∷ ts) = subst σ t ∷ substList σ ts

-- Left-biased "or" for Maybe (Haskell's <|> / Alternative)
--   nothing <|> y = y
--   just x  <|> _ = just x
infixr 3 _<|>_
_<|>_ : {A : Set} → Maybe A → Maybe A → Maybe A
nothing <|> y = y
just x  <|> _ = just x

-- comp s1 s2  corresponds to  fmap (subst s1) s2 `Map.union` s1
-- With function-based substitutions this is simply:
--   • apply s2 first, then apply s1 to the result  (fmap branch)
--   • fall back to s1 if s2 has no binding          (<|> branch)
comp : Substitution → Substitution → Substitution
comp s1 s2 k = Maybe.map (subst s1) (s2 k) <|> s1 k

-- ─── Lemmas ──────────────────────────────────────────────────────────────────

-- Axiom 1 from the Gist:
--   f (fromMaybe d x) = fromMaybe (f d) (fmap f x)
-- Proved by case analysis on x.
fromMaybe-natural : ∀ {A B : Set} (f : A → B) (d : A) (x : Maybe A)
                  → f (fromMaybe d x) ≡ fromMaybe (f d) (Maybe.map f x)
fromMaybe-natural f d nothing  = refl
fromMaybe-natural f d (just _) = refl

-- Axiom 3 from the Gist (restated for function-based maps):
--   fromMaybe (fromMaybe d x) y = fromMaybe d (y <|> x)
-- This captures how left-biased union interacts with fromMaybe.
-- Proved by case analysis on y.
fromMaybe-<|> : ∀ {A : Set} (d : A) (x : Maybe A) (y : Maybe A)
              → fromMaybe (fromMaybe d x) y ≡ fromMaybe d (y <|> x)
fromMaybe-<|> d x nothing  = refl
fromMaybe-<|> d x (just _) = refl

-- ─── Main theorem ────────────────────────────────────────────────────────────

-- Proof outline for the Variable case:
--
--   subst s1 (subst s2 (Variable sym))
--   = subst s1 (fromMaybe (Variable sym) (s2 sym))
--                                                    [fromMaybe-natural]
--   ≡ fromMaybe (subst s1 (Variable sym)) (Maybe.map (subst s1) (s2 sym))
--   = fromMaybe (fromMaybe (Variable sym) (s1 sym)) (Maybe.map (subst s1) (s2 sym))
--                                                    [fromMaybe-<|>]
--   ≡ fromMaybe (Variable sym) (Maybe.map (subst s1) (s2 sym) <|> s1 sym)
--   = fromMaybe (Variable sym) (comp s1 s2 sym)
--   = subst (comp s1 s2) (Variable sym)
--
-- (The Predicate case follows by mutual induction on the list of subterms.)

mutual
  subst-comp : ∀ (s1 s2 : Substitution) (t : Term)
             → subst (comp s1 s2) t ≡ subst s1 (subst s2 t)

  subst-comp s1 s2 (Variable k) =
    sym (trans
      (fromMaybe-natural (subst s1) (Variable k) (s2 k))
      (fromMaybe-<|>     (Variable k) (s1 k)     (Maybe.map (subst s1) (s2 k))))

  subst-comp s1 s2 (Predicate k ts) =
    cong (Predicate k) (substList-comp s1 s2 ts)

  substList-comp : ∀ (s1 s2 : Substitution) (ts : List Term)
                 → substList (comp s1 s2) ts ≡ substList s1 (substList s2 ts)

  substList-comp s1 s2 []       = refl
  substList-comp s1 s2 (t ∷ ts) =
    cong₂ _∷_ (subst-comp s1 s2 t) (substList-comp s1 s2 ts)
