module Demo where

-- n != m of type A
-- when checking that the given dot pattern n matches the inferred
-- value m
-- wrong : {A : Set} → (n m : A) → A
-- wrong n .(n) = n
