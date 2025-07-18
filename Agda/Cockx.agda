-- Agda is too powerful, which is bad for beginners.

module Cockx where

data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
Nat.zero + y = y
suc x + y = suc (x + y)

halve : Nat → Nat
halve zero = zero
halve (suc zero) = zero
halve (suc (suc n)) = suc (halve n)

_*_ : Nat → Nat → Nat
zero * y = zero
Nat.suc x * y = y + (x * y)

data Bool : Set where
  false : Bool
  true : Bool

not : Bool → Bool
not false = true
not true = false

_&&_ : Bool → Bool → Bool
false && _ = false
true && y = y

_||_ : Bool → Bool → Bool
false || y = y
true || _ = true

id : {A : Set} → A → A
id x = x

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

-- infixr 5 _::_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

fst : {A B : Set} → A × B → A
fst (x , _) = x

snd : {A B : Set} → A × B → B
snd (_ , y) = y

length : {A : Set} → List A → Nat
length [] = zero
length (_ :: rest) = suc (length rest)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : {A B : Set} → (A → B) → List A → List B
map _ [] = []
map f (x :: xs) = f x :: map f xs

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

lookup : {A : Set} → List A → Nat → Maybe A
lookup []        _       = nothing
lookup (x :: xs) zero    = just x
lookup (x :: xs) (suc n) = lookup xs n

-- foo : Bool → Bool
-- foo true = false

-- bar : Nat → Nat
-- bar x = bar x

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

infixr 5 _::_

myVec1 : Vec Nat (2 + 3)
myVec1 = 1 :: 2 :: 3 :: 4 :: 5 :: []

myVec2 : Vec (Bool → Bool) 2
myVec2 = not :: id :: []

myVec3 : Vec Nat 0
myVec3 = []

zeroes : (n : Nat) → Vec Nat n
zeroes zero = []
zeroes (suc n) = 0 :: zeroes n

prepend : {n : Nat} → Bool → Vec Bool n → Vec Bool (suc n)
prepend = _::_

downFrom : (n : Nat) → Vec Nat n
downFrom zero = []
downFrom (suc n) = n :: downFrom n

_++Vec_ :
    {A : Set} → {m n : Nat}
  → Vec A m → Vec A n → Vec A (m + n)
[] ++Vec ys = ys
(x :: xs) ++Vec ys = x :: (xs ++Vec ys)

head : {A : Set} {n : Nat} → Vec A (suc n) → A
head (x :: _) = x

tail : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail (_ :: xs) = xs

dotProduct : {n : Nat} → Vec Nat n → Vec Nat n → Nat
dotProduct [] [] = 0
dotProduct (x :: xs) (y :: ys) = (x * y) + dotProduct xs ys

dotProduct' : {n : Nat} → Vec Nat n → Vec Nat n → Nat
dotProduct' {zero} Vec.[] [] = 0
dotProduct' {suc n} (x Vec.:: xs) (y :: ys) = (x * y) + dotProduct' xs ys

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)

lookupVec : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookupVec (x :: xs) zero = x
lookupVec (x :: xs) (suc i) = lookupVec xs i

lookupVec′ : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookupVec′ {_} {suc n} (x :: xs) zero = x
lookupVec′ {_} {suc n} (x :: xs) (suc i) = lookupVec′ xs i

lookupVec″ : {A : Set} {n : Nat} (_ : Vec A n) (_ : Fin n) → A
lookupVec″ (x :: xs) zero = x
lookupVec″ (x :: xs) (suc i) = lookupVec″ xs i

-- lookupVec⁗ : {A : Set} {n : Nat} (Vec A n) (_ : Fin n) → A
-- lookupVec⁗ (x :: xs) zero = x
-- lookupVec⁗ (x :: xs) (suc i) = lookupVec⁗ xs i

-- lookupVec‴ : {A : Set} → {n : Nat} → Vec A n → Fin n → A
-- lookupVec‴ {_} .{suc n} (x :: xs) zero = x
-- lookupVec‴ {_} .{suc n} (x :: xs) (suc i) = lookupVec‴ xs i

putVec : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
putVec zero    new (_ :: xs) = new :: xs
putVec (suc i) new (x :: xs) = x :: putVec i new xs

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

_×′_ : (A B : Set) → Set
A ×′ B = Σ A (λ _ → B)

×-to-×′ : {A B : Set} → A × B → A ×′ B
×-to-×′ (x , y) = (x , y)

×′-to-× : {A B : Set} → A ×′ B → A × B
×′-to-× (x , y) = (x , y)

fstΣ : {A : Set} {B : A → Set} → Σ A B → A
fstΣ (x , _) = x

sndΣ : {A : Set} {B : A → Set} → (z : Σ A B) → B (fstΣ z)
sndΣ (_ , y) = y

-- sndΣ′ : {A : Set} {B : A → Set} → (z : Σ A B) (let (x , _) = z) → B x
-- sndΣ′ (_ , y) = y

List′ : (A : Set) → Set
List′ A = Σ Nat (Vec A)

-- []′ : {A : Set} → List′ A
-- []′ = (Nat.zero, [] {0})

[]′ : {A : Set} → List′ A
[]′ = 0 , []

_::′_ : {A : Set} → A → List′ A → List′ A
element ::′ (length , vec) = (suc length , element :: vec)

List-to-List′ : {A : Set} → List A → List′ A
List-to-List′ [] = []′
List-to-List′ (x :: xs) = x ::′ List-to-List′ xs

List′-to-List : {A : Set} → List′ A → List A
List′-to-List (zero , []) = []
List′-to-List (suc n , x :: xs) = x :: List′-to-List (n , xs)

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left x)  f _ = f x
cases (right y) _ g = g y

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

absurd : {A : Set} → ⊥ → A
absurd ()

module curry-howard where
  _ : {P : Set} → P → P
  _ = λ p → p

  proof1 : {P : Set} → P → P
  proof1 p = p

  proof2
    : {P Q R : Set}
    → (P → Q) × (Q → R)
    → (P → R)
  proof2 (f , g) = λ x → g (f x)

  proof3 : {P Q R : Set} → (Either P Q → R) → (P → R) × (Q → R)
  proof3 f = (λ x → f (left x)) , (λ y → f (right y))

  proof4 : {A B : Set} → A → B → A
  proof4 x _ = x

  proof5 : {A B : Set} → A × ⊤ → Either A ⊥
  proof5 (x , tt) = left x

  proof6 : {A B C : Set} → (A → (B → C)) → (A × B → C)
  proof6 f (x , y) = f x y

  proof7 :
        {A B C : Set}
      → A × Either B C
      → Either (A × B) (A × C)
  proof7 (x , yz) = cases yz (λ y → left (x , y)) (λ z → right (x , z))
  -- proof7 (x , left y)  = left  (x , y)
  -- proof7 (x , right z) = right (x , z)

  proof8 :
      {A B C D : Set}
    → (A → C) × (B → D)
    → (A × B) → (C × D)
  proof8 (f , g) (x , y) = f x , g y

  proof9 : {P : Set} → (Either P (P → ⊥) → ⊥) → ⊥
  proof9 f = f (right (λ p → f (left p)))

data IsEven : Nat → Set where
  zero : IsEven zero
  suc-suc : {n : Nat} → IsEven n → IsEven (suc (suc n))

6-is-even : IsEven 6
6-is-even = suc-suc (suc-suc (suc-suc zero))

7-is-not-even : IsEven 7 → ⊥
7-is-not-even (suc-suc (suc-suc (suc-suc ())))

data IsTrue : Bool → Set where
  TrueIsTrue : IsTrue true

isTrue : Bool → Set
isTrue true  = ⊤
isTrue false = ⊥

_=Nat_ : Nat → Nat → Bool
zero  =Nat zero  = true
suc x =Nat suc y = x =Nat y
_     =Nat _     = false

length-is-3 : IsTrue (length (1 :: (2 :: (3 :: []))) =Nat 3)
length-is-3 = TrueIsTrue

double : Nat → Nat
double zero    = zero
double (suc n) = suc (suc (double n))

double-is-even : (n : Nat) → IsEven (double n)
double-is-even zero = zero
double-is-even (suc x) = suc-suc (double-is-even x)

n-equals-n : (n : Nat) → IsTrue (n =Nat n)
n-equals-n zero = TrueIsTrue
n-equals-n (suc x) = n-equals-n x

half-a-dozen : Σ Nat (λ n → IsTrue ((n + n) =Nat 12))
half-a-dozen = 6 , TrueIsTrue

zero-or-suc :
    (n : Nat)
  → Either (IsTrue (n =Nat 0)) (Σ Nat (λ m → IsTrue (suc m =Nat n)))
zero-or-suc zero = left TrueIsTrue
zero-or-suc (suc x) = right (x , n-equals-n x)

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

infix 4 _≡_

one-plus-one : 1 + 1 ≡ 2
one-plus-one = refl

zero-not-one : 0 ≡ 1 → ⊥
zero-not-one ()

n-not-suc : {n : Nat} → n ≡ suc n → ⊥
n-not-suc ()
-- n-not-suc {zero} ()
-- n-not-suc {suc n} ()

n-not-suc-suc-suc : {n : Nat} → n ≡ suc (suc (suc n)) → ⊥
n-not-suc-suc-suc ()

id-returns-input : {A : Set} → (x : A) → id x ≡ x
id-returns-input x = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

sym′ : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym′ {_} {.a} {.a} (refl {a}) = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

trans′ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ {_} {.a} {.a} {.a} (refl {.a}) (refl {a}) = refl

trans′' : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′' {x = .a} {.a} {.a} (refl {.a}) (refl {a}) = refl

trans″ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans″ h1 refl = h1

trans‴ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans‴ h1 (refl {a}) = h1

trans⁗ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans⁗ (refl {.a}) (refl {a}) = refl {_} {a}

trans⁗' : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans⁗' (refl {.a}) (refl {a}) = refl {x = a}

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- error : {A B : Set} {a1 a2 : A} → (f : A → B) → f a1 ≡ f a2 → a1 ≡ a2
-- error f h = {! h !}
-- I'm not sure if there should be a case for the constructor refl,
-- because I get stuck when trying to solve the following unification
-- problems (inferred index ≟ expected index):
--   x ≟ f₁ a3
--   x ≟ f₁ a3
-- when checking that the expression ? has type a1 ≡ a2

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix 1 begin_
infix 3 _end
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_

[_] : {A : Set} → A → List A
[ x ] = x :: []

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

reverse-singleton : {A : Set} (x : A) → reverse [ x ] ≡ [ x ]
-- reverse-singleton x = refl
reverse-singleton x =
  begin
    reverse [ x ]
  =⟨⟩
    reverse (x :: [])
  =⟨⟩
    reverse [] ++ [ x ]
  =⟨⟩
    [] ++ [ x ]
  =⟨⟩
    [ x ]
  end

not-not : (b : Bool) → not (not b) ≡ b
not-not false =
  begin
    not (not false)
  =⟨⟩
    not true
  =⟨⟩
    false
  end
not-not true =
  begin
    not (not true)
  =⟨⟩
    not false
  =⟨⟩
    true
  end

add-n-zero : (n : Nat) → n + zero ≡ n
add-n-zero zero =
  begin
    zero + zero
  =⟨⟩
    zero
  end
add-n-zero (suc n) =
  begin
    suc n + zero
  =⟨⟩
    suc (n + zero)
  =⟨ cong suc (add-n-zero n) ⟩
    suc n
  end

add-n-suc : (n m : Nat) → n + suc m ≡ suc (n + m)
add-n-suc zero m =
  begin
    zero + suc m
  =⟨⟩
    suc m
  =⟨⟩
    suc (zero + m)
  end
add-n-suc (suc n) m =
  begin
    suc n + suc m
  =⟨⟩
    suc (n + suc m)
  =⟨ cong suc (add-n-suc n m) ⟩
    suc (suc (n + m))
  =⟨⟩
    suc (suc n + m)
  end

add-assoc : (x y z : Nat) → x + (y + z) ≡ (x + y) + z
add-assoc zero y z =
  begin
    zero + (y + z)
  =⟨⟩
    y + z
  =⟨⟩
    (zero + y) + z
  end
add-assoc (suc x) y z =
  begin
    suc x + (y + z)
  =⟨⟩
    suc (x + (y + z))
  =⟨ cong suc (add-assoc x y z) ⟩
    suc ((x + y) + z)
  =⟨⟩
    suc (x + y) + z
  =⟨⟩
    (suc x + y) + z
  end

replicate : {A : Set}
  → Nat → A → List A
replicate zero _ = []
replicate (suc n) x = x :: replicate n x

length-replicate : {A : Set} → (n : Nat) → (x : A) → length (replicate n x) ≡ n
length-replicate {A} zero x =
  begin
    length (replicate zero x)
  =⟨⟩
    length  ([] {A})
  =⟨⟩
    zero
  end
length-replicate (suc n) x =
  begin
    length (replicate (suc n) x)
  =⟨⟩
    length (x :: replicate n x)
  =⟨⟩
    suc (length (replicate n x))
  =⟨ cong suc (length-replicate n x) ⟩
    suc n
  end


append-[] : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
append-[] [] =
  begin
    [] ++ []
  =⟨⟩
    []
  end
append-[] (x :: xs) =
  begin
    x :: xs ++ []
  =⟨⟩
    x :: (xs ++ [])
  =⟨ cong (x ::_) (append-[] xs) ⟩
    x :: xs
  end

++-assoc : {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  =⟨⟩
    ys ++ zs
  =⟨⟩
    [] ++ (ys ++ zs)
  end
++-assoc (x :: xs) ys zs =
  begin
    (x :: xs ++ ys) ++ zs
  =⟨⟩
    x :: (xs ++ ys) ++ zs
  =⟨⟩
    x :: ((xs ++ ys) ++ zs)
  =⟨ cong (x ::_) (++-assoc xs ys zs) ⟩
    x :: (xs ++ (ys ++ zs))
  =⟨⟩
    x :: xs ++ (ys ++ zs)
  end

reverse-distributivity :
    {A : Set} → (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-distributivity [] ys =
  begin
    reverse ([] ++ ys)
  =⟨⟩
    reverse ys
  =⟨ sym (append-[] (reverse ys)) ⟩
    reverse ys ++ []
  =⟨⟩
    reverse ys ++ reverse []
  end
reverse-distributivity (x :: xs) ys =
  begin
    reverse (x :: xs ++ ys)
  =⟨⟩
    reverse (x :: (xs ++ ys))
  =⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  =⟨ cong (_++ [ x ]) (reverse-distributivity xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  =⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  =⟨⟩
    reverse ys ++ (reverse (x :: xs))
  end

reverse-reverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse [] =
  begin
    reverse (reverse [])
  =⟨⟩
    reverse []
  =⟨⟩
    []
  end
reverse-reverse (x :: xs) =
  begin
    reverse (reverse (x :: xs))
  =⟨⟩
    reverse (reverse xs ++ [ x ])
  =⟨ reverse-distributivity (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs)
  =⟨ cong (_++ reverse (reverse xs)) (reverse-singleton x) ⟩
    [ x ] ++ reverse (reverse xs)
  =⟨⟩
    x :: reverse (reverse xs)
  =⟨ cong (x ::_) (reverse-reverse xs) ⟩
    x :: xs
  end

map-id : {A : Set} (xs : List A) → map id xs ≡ xs
map-id [] =
  begin
    map id []
  =⟨⟩
    []
  end
map-id (x :: xs) =
  begin
    map id (x :: xs)
  =⟨⟩
    id x :: map id xs
  =⟨⟩
    x :: map id xs
  =⟨ cong (x ::_) (map-id xs) ⟩
    x :: xs
  end

_◦_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ◦ f = λ x → g (f x)

map-compose :
    {A B C : Set} (f : B → C) (g : A → B) (xs : List A)
  → map (f ◦ g) xs ≡ map f (map g xs)
map-compose f g [] =
  begin
    map (f ◦ g) []
  =⟨⟩
    []
  =⟨⟩
    map f []
  =⟨⟩
    map f (map g [])
  end
map-compose f g (x :: xs) =
  begin
    map (f ◦ g) (x :: xs)
  =⟨⟩
    (f ◦ g) x :: map (f ◦ g) xs
  =⟨⟩
    f (g x) :: map (f ◦ g) xs
  =⟨ cong (f (g x) ::_) (map-compose f g xs) ⟩
    f (g x) :: map f (map g xs)
  =⟨⟩
    map f (g x :: map g xs)
  =⟨⟩
    map f (map g (x :: xs))
  end

length-map : {A B : Set} → (f : A → B) → (xs : List A) → length (map f xs) ≡ length xs
length-map {A} f [] =
  begin
    length (map f [])
  =⟨⟩
    length ([] {A})
  end
length-map f (x :: xs) =
  begin
    length (map f (x :: xs))
  =⟨⟩
    length (f x :: map f xs)
  =⟨⟩
    suc (length (map f xs))
  =⟨ cong suc (length-map f xs) ⟩
    suc (length xs)
  =⟨⟩
    length (x :: xs)
  end

take : {A : Set} → Nat → List A → List A
take zero    _         = []
take (suc n) []        = []
take (suc n) (x :: xs) = x :: take n xs

drop : {A : Set} → Nat → List A → List A
drop zero    xs        = xs
drop (suc n) []        = []
drop (suc n) (_ :: xs) = drop n xs

take-drop : {A : Set} → (n : Nat) → (xs : List A) → take n xs ++ drop n xs ≡ xs
take-drop zero xs =
  begin
    take zero xs ++ drop zero xs
  =⟨⟩
    [] ++ xs
  =⟨⟩
    xs
  end
take-drop (suc n) [] =
  begin
    take (suc n) [] ++ drop (suc n) []
  =⟨⟩
    [] ++ []
  =⟨⟩
    []
  end
take-drop (suc n) (x :: xs) =
  begin
    take (suc n) (x :: xs) ++ drop (suc n) (x :: xs)
  =⟨⟩
    x :: take n xs ++ drop n xs
  =⟨⟩
    x :: (take n xs ++ drop n xs)
  =⟨ cong (x ::_) (take-drop n xs) ⟩
    x :: xs
  end

reverse-acc : {A : Set} → List A → List A → List A
reverse-acc []        ys = ys
reverse-acc (x :: xs) ys = reverse-acc xs (x :: ys)

reverse′ : {A : Set} → List A → List A
reverse′ xs = reverse-acc xs []

reverse′-reverse : {A : Set} → (xs : List A) → reverse′ xs ≡ reverse xs
reverse′-reverse xs =
  begin
    reverse′ xs
  =⟨⟩
    reverse-acc xs []
  =⟨ reverse-acc-reverse xs [] ⟩
    reverse xs ++ []
  =⟨ append-[] (reverse xs) ⟩
    reverse xs
  end
  where
    reverse-acc-reverse : {A : Set} → (xs ys : List A) → reverse-acc xs ys ≡ reverse xs ++ ys
    reverse-acc-reverse [] ys =
      begin
        reverse-acc [] ys
      =⟨⟩
        ys
      =⟨⟩
        [] ++ ys
      =⟨⟩
        reverse [] ++ ys
      end
    reverse-acc-reverse (x :: xs) ys =
      begin
        reverse-acc (x :: xs) ys
      =⟨⟩
        reverse-acc xs (x :: ys)
      =⟨ reverse-acc-reverse xs (x :: ys) ⟩
        reverse xs ++ (x :: ys)
      =⟨⟩
        reverse xs ++ ([ x ] ++ ys)
      =⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
        (reverse xs ++ [ x ]) ++ ys
      =⟨⟩
        reverse (x :: xs) ++ ys
      end

data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

flatten : {A : Set} → Tree A → List A
flatten (leaf x) = [ x ]
flatten (node t t₁) = flatten t ++ flatten t₁

flatten-acc : {A : Set} → Tree A → List A → List A
flatten-acc (leaf x)     xs = x :: xs
flatten-acc (node t₁ t₂) xs = flatten-acc t₁ (flatten-acc t₂ xs)

flatten′ : {A : Set} → Tree A → List A
flatten′ t = flatten-acc t []

flatten-acc-flatten : {A : Set} → (t : Tree A) → (xs : List A) → flatten-acc t xs ≡ flatten t ++ xs
flatten-acc-flatten (leaf x)    xs =
  begin
    flatten-acc (leaf x) xs
  =⟨⟩
    x :: xs
  end
flatten-acc-flatten (node t t₁) xs =
  begin
    flatten-acc (node t t₁) xs
  =⟨⟩
    flatten-acc t (flatten-acc t₁ xs)
  =⟨ cong (flatten-acc t) (flatten-acc-flatten t₁ xs) ⟩
    flatten-acc t (flatten t₁ ++ xs)
  =⟨ flatten-acc-flatten t (flatten t₁ ++ xs) ⟩
    flatten t ++ (flatten t₁ ++ xs)
  =⟨ sym (++-assoc (flatten t) (flatten t₁) xs) ⟩
    (flatten t ++ flatten t₁) ++ xs
  =⟨⟩
    flatten (node t t₁) ++ xs
  end

flatten′-flatten : {A : Set} → (t : Tree A) → flatten′ t ≡ flatten t
flatten′-flatten t =
  begin
    flatten′ t
  =⟨⟩
    flatten-acc t []
  =⟨ flatten-acc-flatten t [] ⟩
    flatten t ++ []
  =⟨ append-[] (flatten t) ⟩
    flatten t
  end

data Expr : Set where
  valE : Nat → Expr
  addE : Expr → Expr → Expr

eval : Expr → Nat
eval (valE x) = x
eval (addE e e₁) = eval e + eval e₁

data Op : Set where
  PUSH : Nat → Op
  ADD : Op

Stack = List Nat
Code = List Op

exec : Code → Stack → Stack
exec []            s             = s
exec (PUSH x :: c) s             = exec c (x :: s)
exec (ADD :: c)    (m :: n :: s) = exec c (n + m :: s)
exec (ADD :: c)    _             = []


compile′ : Expr → Code → Code
compile′ (valE x)    c = PUSH x :: c
compile′ (addE e e₁) c = compile′ e (compile′ e₁ (ADD :: c))

compile : Expr → Code
compile e = compile′ e []

compile′-exec-eval :
    (e : Expr) (s : Stack) (c : Code)
  → exec (compile′ e c) s ≡ exec c (eval e :: s)
compile′-exec-eval (valE x) s c =
  begin
    exec (compile′ (valE x) c) s
  =⟨⟩
    exec (PUSH x :: c) s
  =⟨⟩
    exec c (x :: s)
  =⟨⟩
    exec c (eval (valE x) :: s)
  end
compile′-exec-eval (addE e e₁) s c =
  begin
    exec (compile′ (addE e e₁) c) s
  =⟨⟩
    exec (compile′ e (compile′ e₁ (ADD :: c))) s
  =⟨ compile′-exec-eval e s (compile′ e₁ (ADD :: c)) ⟩
    exec (compile′ e₁ (ADD :: c)) (eval e :: s)
  =⟨ compile′-exec-eval e₁ (eval e :: s) (ADD :: c) ⟩
    exec (ADD :: c) (eval e₁ :: (eval e :: s))
  =⟨⟩
    exec c ((eval e + eval e₁) :: s)
  =⟨⟩
    exec c (eval (addE e e₁) :: s)
  end
