module NoConfusionEncodeDecode where


open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
-- open import 
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

infix 4 _≡_
data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

data ⊥ : Set where
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- infix 4 _≡_
-- data _≡_ {A : Set} (x : A) : A → Set where
--   refl : x ≡ x

cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

data Ty : Set where
  TyNat  : Ty
  TyBool : Ty

data Expr : Ty → Set where
  lit  : ℕ → Expr TyNat
  add  : Expr TyNat → Expr TyNat → Expr TyNat
  bval : Bool → Expr TyBool
  if_  : ∀ {t : Ty} → Expr TyBool → Expr t → Expr t → Expr t

Code : ∀ {t : Ty} → Expr t → Expr t → Set
Code (lit m)     (lit n)     = m ≡ n
-- Code (lit m)     (add x y)   = ⊥
-- Code (add x y)   (lit m)     = ⊥
Code (add x₁ x₂) (add y₁ y₂) = (x₁ ≡ y₁) × (x₂ ≡ y₂)
Code (bval b)    (bval b')   = b ≡ b'
-- Code (bval b)    (if_ c x y) = ⊥
-- Code (if_ c x y) (bval b')   = ⊥
Code (if_ c₁ x₁ y₁) (if_ c₂ x₂ y₂) = (c₁ ≡ c₂) × (x₁ ≡ x₂) × (y₁ ≡ y₂)
Code _ _ = ⊥

codeRefl : ∀ {t : Ty} (x : Expr t) → Code x x
codeRefl (lit m)     = refl
codeRefl (add x y)   = (refl , refl)
codeRefl (bval b)    = refl
codeRefl (if_ c x y) = (refl , (refl , refl))

encode : ∀ {t : Ty} {x y : Expr t} → x ≡ y → Code x y
encode refl = codeRefl _

subst₂ : ∀ {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B}
       → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
subst₂ f refl refl = refl

subst₃ : ∀ {A B C D : Set} (f : A → B → C → D)
       {a a' : A} {b b' : B} {c c' : C}
       → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
subst₃ f refl refl refl = refl

decode : ∀ {t : Ty} {x y : Expr t} → Code x y → x ≡ y
decode {x = lit m}     {y = lit n}     p = cong lit p
-- decode {x = lit m}     {y = add x y}   ()
-- decode {x = add x y}   {y = lit m}     ()
decode {x = add x₁ x₂} {y = add y₁ y₂} p =
  -- p : (x₁≡y₁) × (x₂≡y₂)
  -- 用两次 subst/cong 也行；这里给最直观写法：
  subst₂ add (fst p) (snd p)
decode {x = bval b}    {y = bval b'}   p = cong bval p
-- decode {x = bval b}    {y = if_ c x y} ()
-- decode {x = if_ c x y} {y = bval b'}   ()
decode {x = if_ c₁ x₁ y₁} {y = if_ c₂ x₂ y₂} p =
  subst₃ if_ (fst p) (fst (snd p)) (snd (snd p))

lit-inj : ∀ {m n : ℕ} → lit m ≡ lit n → m ≡ n
lit-inj p = encode p  -- 因为 Code (lit m) (lit n) 定义就是 m≡n

add-inj : ∀ {x₁ x₂ y₁ y₂ : Expr TyNat}
        → add x₁ x₂ ≡ add y₁ y₂ → (x₁ ≡ y₁) × (x₂ ≡ y₂)
add-inj p = encode p

lit≢add : ∀ {m : ℕ} {x y : Expr TyNat} → lit m ≡ add x y → ⊥
lit≢add p = encode p  -- 因为 Code (lit m) (add x y) 定义就是 ⊥

-- decode-encode : ∀ {t : Ty} {x y : Expr t} (p : x ≡ y)
--               → decode (encode p) ≡ p
-- decode-encode refl = refl
decode-encode : ∀ {t : Ty} {x y : Expr t} (p : x ≡ y)
              → decode (encode p) ≡ p
decode-encode {x = x} refl = helper x
  where
    helper : ∀ {t : Ty} (x : Expr t) → decode (codeRefl x) ≡ refl
    helper (lit m)     = refl
    helper (add x y)   = refl
    helper (bval b)    = refl
    helper (if_ c x y) = refl

-- encode-decode : ∀ {t : Ty} {x y : Expr t} (c : Code x y)
--               → encode (decode c) ≡ c
-- encode-decode {x = lit m}     {y = lit n}     refl =
--   -- c : m≡n
--   -- decode c = cong lit c; encode 再回来应该是 c
--   -- 这里一般靠“等式唯一计算到 refl”的归约；写成 refl 即可（Agda 会算）
--   refl

-- encode-decode {x = lit m}     {y = add x y}   ()
-- encode-decode {x = add x y}   {y = lit m}     ()
-- encode-decode {x = add x₁ x₂} {y = add y₁ y₂} (refl , refl) = refl

-- encode-decode {x = bval b}    {y = bval b'}   refl = refl
-- encode-decode {x = bval b}    {y = if_ c x y} ()
-- encode-decode {x = if_ c x y} {y = bval b'}   ()
-- encode-decode {x = if_ c₁ x₁ y₁} {y = if_ c₂ x₂ y₂} (refl , (refl , refl)) = refl

-- encode-decode : ∀ {t : Ty} {x y : Expr t} (c : Code x y)
--               → encode (decode c) ≡ c
-- encode-decode {x = lit m} {y = lit n} c with c
-- ... | refl = refl
-- encode-decode {x = bval b} {y = bval b'} c with c
-- ... | refl = refl
-- encode-decode {x = add x₁ x₂} {y = add y₁ y₂} (p , q) with p | q
-- ... | refl | refl = refl
-- encode-decode {x = if_ c₁ x₁ y₁} {y = if_ c₂ x₂ y₂} (p , (q , r)) with p | q | r
-- ... | refl | refl | refl = refl

-- encode-decode : ∀ {t : Ty} {x y : Expr t} (c : Code x y)
--               → encode (decode c) ≡ c
-- encode-decode c with c
-- -- Cannot split on argument of non-datatype Code x y
-- -- when checking that the pattern refl has type Code x y
-- ... | refl = refl

_ : (1 ≡ 2) ≡ (1 ≡ 2)
_ = refl
