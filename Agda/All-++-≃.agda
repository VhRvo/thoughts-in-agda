module All-++-≃ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import plfa.part1.Lists using (List; []; _∷_; _++_; All)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)

open import Data.Nat
-- open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_; Dec; yes; no)

data Empty : Set where

pass : {A : Set} (f1 f2 : A → ⊥) → f1 ≡ f2
pass f1 f2 = refl

fail : {A : Set} (f1 f2 : A → Empty) → f1 ≡ f2
fail f1 f2 = refl

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ {A} {P} xs ys =
  record
    { to    =  to xs ys
    ; from  =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys)
    with to xs ys Pxs++ys
  ...  | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  helper1 : (x : A) (xs ys : List A) (Px : P x) (Pxs++ys : All P (xs ++ ys))
      (Pxs : All P xs ) (Pys : All P ys)
    → (⟨ Pxs , Pys ⟩ ≡ to xs ys Pxs++ys)
    → (to (x ∷ xs) ys (Px ∷ Pxs++ys)) ≡ ⟨ Px ∷ proj₁ (to xs ys Pxs++ys) , proj₂ (to xs ys Pxs++ys) ⟩
  helper1 x xs ys Px Pxs++ys
    Pxs Pys eq
    = refl

  helper3 : (x : A) (xs ys : List A) (Px : P x) (Pxs++ys : All P (xs ++ ys))
      (Pxs,Pys : All P xs × All P ys)
    → (Pxs,Pys ≡ to xs ys Pxs++ys)
    → (to (x ∷ xs) ys (Px ∷ Pxs++ys)) ≡ ⟨ Px ∷ proj₁ Pxs,Pys , proj₂ Pxs,Pys ⟩
  helper3 x xs ys Px Pxs++ys
    Pxs,Pys refl
    = refl

  helper2 : (x : A) (xs ys : List A) (Px : P x) (Pxs++ys : All P (xs ++ ys))
      (Pxs : All P xs ) (Pys : All P ys)
    → (⟨ Pxs , Pys ⟩ ≡ to xs ys Pxs++ys)
    → (to (x ∷ xs) ys (Px ∷ Pxs++ys)) ≡ ⟨ Px ∷ Pxs , Pys ⟩
  helper2 x xs ys Px Pxs++ys
    Pxs Pys refl
    = refl

  helper : (x : A) (xs ys : List A) (Px : P x) (Pxs++ys : All P (xs ++ ys)) (Pxs : All P xs ) (Pys : All P ys)
    → (⟨ Pxs , Pys ⟩ ≡ to xs ys Pxs++ys)
    → (to (x ∷ xs) ys (Px ∷ Pxs++ys)) ≡ ⟨ Px ∷ Pxs , Pys ⟩
  helper x xs ys Px Pxs++ys Pxs Pys refl = refl -- {! refl  !}
    -- begin
    --   from (x ∷ xs) ys (to (x ∷ xs) ys (Px ∷ Pxs++ys))
    -- ≡⟨⟩
    --   from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩
    -- ≡⟨⟩
    --   Px ∷ from xs ys ⟨ Pxs , Pys ⟩
    -- ∎


  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩
