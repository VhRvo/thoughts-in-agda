module First where

data Answer : Set where
    yes : Answer
    no : Answer
    maybe : Answer

data Quarter : Set where
    east : Quarter
    west : Quarter
    north : Quarter
    south : Quarter

-- Interpretation (or meaning) is the opposite relation to representation.
-- Representation are about syntax
-- Interpretation are about semantics

data ⊥ : Set where

data ⊤ : Set where
    tt : ⊤
