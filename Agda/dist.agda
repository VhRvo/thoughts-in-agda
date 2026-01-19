module dist where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂)
open Eq.≡-Reasoning
  using (begin_; _∎; step-≡-∣; step-≡-⟩)
open import Data.Product.Base
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_; contradiction)

postulate
  em : ∀ {A : Set} → ¬ A ⊎ A
  ¬¬-elim : ∀ {A : Set} → ¬ ¬ A → A

dist-inv :
    {A B C : Set}
  → (A → B) ⊎ (A → C)
  → A → (B ⊎ C)
dist-inv (inj₁ f) x = inj₁ (f x)
dist-inv (inj₂ g) x = inj₂ (g x)

dist :
    {A B C : Set}
  → (A → (B ⊎ C))
  → (A → B) ⊎ (A → C)
dist f with em
...       | inj₁ ¬a  =  inj₁ (λ a → contradiction a ¬a)
...       | inj₂  a with f a
...                    | inj₁ b  =  inj₁ (λ _ → b)
...                    | inj₂ c  =  inj₂ (λ _ → c)

id₁ :
    {A B C : Set}
  → (a : A)
  → (f : A → (B ⊎ C))
  → dist-inv (dist f) a ≡ f a
id₁ a f = {!   !}

id₂ :
    {A B C : Set}
  → (union : (A → B) ⊎ (A → C))
  → dist (dist-inv union) ≡ union
id₂ (inj₁ f) = {!   !}
id₂ (inj₂ g) = {!   !}

-- (v ↦ w) ⊔ (v ↦ w′)
-- ⊑
-- v ↦ (w ⊔ w′)

-- w
-- ⊑
-- (w ⊔ w′)

-- v ↦ w
-- ⊑
-- v ↦ (w ⊔ w′)

