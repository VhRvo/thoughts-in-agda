module Sets.Parametric where

open import Data.Nat
open import Sets.Enumerated using (⊤; tt; Bool; true; false)

data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

infixr 5 _::_

{-
data NList (n : ℕ) : Set where
    [] : NList n
    -- ℕ should be a sort, but it isn't
    _::_ : n → NList n → NList n

nlist1 : NList 2
nlist1 = []

nlist2 : NList 4
nlist2 = []
-}

data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

data BinTree (A : Set) : Set where
    leaf : BinTree A
    node : A → BinTree A → BinTree A → BinTree A

data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt

data Top : Set where
    top : Top

data _⊎_ (A B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

infixr 1 _⊎_

data Bottom : Set where

Maybe₁ : Set → Set
Maybe₁ A = A ⊎ ⊤

data List₁ (A B : Set) : Set
data List₂ (A B : Set) : Set

data List₁ A B where
  []  :                 List₁ A B
  _∷_ : A → List₂ A B → List₁ A B

data List₂ A B where
  _∷_ : B → List₁ A B → List₂ A B

_ = ⊤
  where
    first second third fourth fifth : List₁ ⊤ Bool
    first = []
    second = tt ∷ (false ∷ [])
    third = tt ∷ (true ∷ [])
    fourth = tt ∷ (false ∷ (tt ∷ (false ∷ [])))
    fifth = tt ∷ (false ∷ (tt ∷ (true ∷ [])))

data AlterList (A B : Set) : Set  where
  []  :                     AlterList A B
  _∷_ : A → AlterList B A → AlterList A B

_ = ⊤
  where
    first second third fourth : AlterList ⊤ Bool
    first = []
    second = tt ∷ []
    third = tt ∷ (false ∷ [])
    fourth = tt ∷ (true ∷ [])

_ = ⊤
  where
    first second third fourth : AlterList Bool ⊤
    first = []
    second = false ∷ []
    third = true ∷ []
    fourth = false ∷ (tt ∷ [])

data T4 (A : Set) : Set where
    quad : A → A → A → A → T4 A

data Square (A : Set) : Set where
    zero : A → Square A
    suc : Square (T4 A) → Square A

