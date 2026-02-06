module TwoIndexesEq where

data _≡_ {A : Set} : A -> A → Set where
    refl : {x : A} -> x ≡ x

symm : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
symm {A} {.x} {.x} (refl {x}) = refl

