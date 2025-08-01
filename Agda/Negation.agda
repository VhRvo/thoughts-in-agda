open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List using (List; []; _∷_; _++_; [_]; map)

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B : Set} → (A → B) → F A → F B

instance
  ListFunctor₁ : Functor List
  ListFunctor₁ = record { fmap = map }

instance
  ListFunctor₂ : Functor List
  Functor.fmap ListFunctor₂ = map
--   Functor.fmap {{ListFunctor₂}} = map


postulate
  ¬¬-elim : ∀ {A : Set} → ¬ ¬ A → A

quantifier₁ :
    ∀ {A : Set} {P : A → Set} →
    (f : (x : A) → P x) →
    ¬ (Σ A λ a → ¬ P a)
quantifier₁ f ⟨ x , Px ⟩ = contradiction (f x) Px

quantifier₂ :
    ∀ {A : Set} {P : A → Set} →
    (Σ A λ a → P a) →
    ¬ ((x : A) → ¬ P x)
quantifier₂ ⟨ x , Px ⟩ f = contradiction Px (f x)

quantifier₃ :
    ∀ {A : Set} {P : A → Set} →
    (¬ Σ A λ a → ¬ P a) →
    ((x : A) → P x)
quantifier₃ f x  =  ¬¬-elim (λ ¬Px → f ⟨ x , ¬Px ⟩)

quantifier₄ :
    ∀ {A : Set} {P : A → Set} →
    ¬ ((x : A) → ¬ P x) →
    (Σ A λ a → P a)
quantifier₄ f  =  ¬¬-elim (λ ¬∃xPx → f (λ x → λ Px → ¬∃xPx ⟨ x , Px ⟩ ))

postulate
  MarkowPrinciple :
    ∀ {A : Set} {P : A → Set} →
    (f : (x : A) → P x ⊎ ¬ (P x)) →
    ¬ ¬ (Σ A P) → Σ A P

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

DecLem :
  ∀ {A : Set} {P : A → Set} →
  ((x : A) → Dec (P x)) →
  (x : A) → P x ⊎ ¬ P x
DecLem f x with f x
...           | yes Px = inj₁  Px
...           | no ¬Px = inj₂ ¬Px

Decℕ : (a b : ℕ) → Dec (a ≡ b)
Decℕ zero zero = yes refl
Decℕ zero (suc b) = no (λ ())
Decℕ (suc a) zero = no (λ ())
Decℕ (suc a) (suc b)
  with Decℕ a b
...  | yes refl  =  yes refl
...  | no  a≢b   =  no (λ{ refl → a≢b refl })

¬¬-elim-ℕ-lemma : (a : ℕ) → Dec (Σ ℕ (λ b → a ≡ b))
¬¬-elim-ℕ-lemma a  =  yes ⟨ a , refl ⟩

¬¬-elim-ℕ : ¬ ¬ (Σ ℕ (λ a → Σ ℕ (λ b → a ≡ b))) → Σ ℕ (λ a → Σ ℕ (λ b → a ≡ b))
¬¬-elim-ℕ dn = MarkowPrinciple (DecLem ¬¬-elim-ℕ-lemma) dn

MarkowClassically :
  ∀ {A : Set} {P : A → Set} →
  (f : (x : A) → P x ⊎ ¬ (P x)) →
  ¬ ¬ (Σ A P) → Σ A P
MarkowClassically f ¬¬ = ¬¬-elim ¬¬

data IsReverse {A : Set} : (xs ys : List A) → Set where
    ReverseNil : IsReverse [] []
    ReverseCons : (x : A) (xs ys : List A)
        → IsReverse xs ys
        → IsReverse (x ∷ xs) (ys ++ [ x ])

theoremReverse₁ : {A : Set} (xs : List A) → Σ (List A) (λ ys → IsReverse xs ys)
theoremReverse₁ [] = ⟨ [] , ReverseNil ⟩
theoremReverse₁ (x ∷ xs) =
    let ⟨ ys , proof ⟩ = theoremReverse₁ xs
    in
      ⟨ ys ++ [ x ] , ReverseCons x xs ys proof ⟩

-- We proved that the nonexistence of the desired list leads to a contradiction,
-- so we concluded that the required list exists using double negation elimination.
theoremReverse₂ : ∀ {A : Set} (xs : List A) →
    Σ (List A) λ ys → IsReverse xs ys
theoremReverse₂ [] = ¬¬-elim (λ p → p ⟨ [] , ReverseNil ⟩)
theoremReverse₂ (x ∷ xs) =
    ¬¬-elim
      (λ p →
        let ⟨ ys , proof ⟩ = theoremReverse₂ xs
        in
        p ⟨ ys ++ [ x ] , ReverseCons x xs ys proof ⟩)

record Ring (R : Set) : Set₁ where
  constructor mkRing
  infixr 7 _·_
  infixr 6 _+_
  field
      θ : R
      -_ : R → R
      _+_ : R → R → R
      _·_ : R → R → R
      +-assoc : (a b c : R) → (a + b) + c ≡ a + (b + c)
      +-commute : (a b : R) → a + b ≡ b + a
      +-inv₁ : (a : R) → - a + a ≡ θ
      +-θ : (a : R) → a + θ ≡ a
      ·-distr-right : (a b c : R) → (a + b) · c ≡ (a · c) + (b · c)
      ·-distr-left : (a b c : R) → a · (b + c) ≡ (a · b) + (a · c)
open Ring {{...}} public

record LieRing (R : Set){{ring : Ring R}} : Set₁ where
  constructor mkLeeRing
  field
    alternation : (a : R) → a · a ≡ θ
    jacobiIdentity : (a b c : R) → (a · b) · c + b · (c · a) + c · (a · b) ≡ θ

-- lemma : {R : Set} → {{Ring R}} (a b : R) → (a + b) · (a + b) ≡ (a · b) + (b · a)
-- lemma a b =
--   begin
--     (a + b) · (a + b)
--   ≡⟨ ·-distr-right a b (a + b) ⟩
--     a · (a + b) + b · (a + b)
--   ≡⟨ cong₂ _+_ (·-distr-left a a b) (·-distr-left b a b) ⟩
--     (a · a + a · b) + (b · a + b · b)
--   ≡⟨ cong (_+_ (a · a + a · b)) (cong₂ _+_ refl (alternation b)) ⟩
--     (a · a + a · b) +  (b · a + θ)
--   ≡⟨ cong (_+_ (a · a + a · b)) (+-θ (b · a)) ⟩
--     (a · a + a · b) + (b · a)
--   ≡⟨ cong₂ _+_ (cong₂ _+_ (alternation a) refl) refl ⟩
--     (θ + a · b) + (b · a)
--   ≡⟨ cong₂ _+_ (trans (+-commute θ (a · b)) (+-θ (a · b))) refl ⟩
--     (a · b + b · a)
--   ∎