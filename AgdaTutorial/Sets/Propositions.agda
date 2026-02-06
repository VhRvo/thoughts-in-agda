module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt

⊤×⊥ : ⊤ × ⊥ → ⊥
⊤×⊥ (tt , ())

⊥×⊥ : ⊥ × ⊥ → ⊥
⊥×⊥ (() , ())

⊤⊎⊤ : ⊤ ⊎ ⊤
⊤⊎⊤ = inj₁ tt

⊤⊎⊥ : ⊤ ⊎ ⊥
⊤⊎⊥ = inj₁ tt

⊥⊎⊥ : ⊥ ⊎ ⊥ → ⊥
⊥⊎⊥ (inj₁ ())
⊥⊎⊥ (inj₂ ())

proof : ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤
proof = inj₂ (inj₁ tt)

data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m : ℕ} → {n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

3≤7 : 3 ≤ 7
3≤7 = s≤s (s≤s (s≤s z≤n))

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))

4≰2 : 4 ≤ 2 → ⊥
4≰2 (s≤s (s≤s ()))

8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s x) = 7≰3 x

-- 以下三个定义（Di、Dj、D）的模式都缺少 (suc zero) 这个 case，
-- 但 Agda 覆盖检查器（coverage checker）的行为因定义所处上下文不同而不同：
--
-- [实验结论]
--   1. 顶层定义（如 Di）                 → 报 missing cases
--   2. where 子句，外层参数类型非空（如 Dj） → 报 missing cases
--   3. where 子句，外层参数类型为空（如 D）  → 不报 missing cases
--
-- 原因：当外层函数的参数类型是空类型（如 ⊥ 或 1 isDoubleOf 0）时，
-- 该函数体（包括 where 子句）是不可达代码（dead code），
-- Agda 的覆盖检查器会跳过其中辅助定义的完整性检查。
--
-- 注意：这一行为未在官方文档中显式记录，是覆盖检查算法的隐含行为。
-- 相关资源：
--   - 覆盖检查文档：https://agda.readthedocs.io/en/latest/language/coverage-checking.html
--   - 论文：Elaborating dependent (co)pattern matching: No pattern left behind (Cockx et al.)
--   - GitHub Issue #2426：https://github.com/agda/agda/issues/2426

-- [案例 1] 顶层定义：Agda 报 missing cases（缺少 Di (suc zero) _）
Di : ℕ → ℕ → Set
Di 0 _ = ⊤
Di (suc (suc _)) 0 = ⊥
Di (suc (suc _)) (suc _) = ⊤

-- [案例 2] where 子句，外层类型 Di 0 0 = ⊤ 非空：Agda 报 missing cases（缺少 Dj (suc zero) _）
dj : Di 0 0
dj = tt
  where
    Dj : ℕ → ℕ → Set
    Dj 0 _ = ⊤
    Dj (suc (suc _)) 0 = ⊥
    Dj (suc (suc _)) (suc _) = ⊤

module IsDoubleOf where
    open import Agda.Builtin.Equality
    data _isDoubleOf_ : ℕ → ℕ → Set where
        base : 0 isDoubleOf 0
        step : {m : ℕ} → {n : ℕ} → m isDoubleOf n → (suc (suc m)) isDoubleOf (suc n)

    8isDoubleOf4 : 8 isDoubleOf 4
    8isDoubleOf4 = step (step (step (step base)))

    9isNotDoubleOf4 : 9 isDoubleOf 4 → ⊥
    9isNotDoubleOf4 (step (step (step (step ()))))

    1isNotDoubleOf0 : 1 isDoubleOf 0 → ⊥
    1isNotDoubleOf0 ()

    ind :
        (Motive : ℕ → ℕ → Set) →
        (baseCase : Motive 0 0) →
        (stepCase : {m n : ℕ} → Motive m n → Motive (suc (suc m)) (suc n)) →
        {m n : ℕ} →
        m isDoubleOf n →
        Motive m n
    ind Motive baseCase stepCase base = baseCase
    ind Motive baseCase stepCase (step x) = stepCase (ind Motive baseCase stepCase x)

    1isNotDoubleOf0′ : 1 isDoubleOf 0 → ⊥
    1isNotDoubleOf0′ proof = ind (\m n → (m ≡ 1 × n ≡ 0) → ⊥) baseCase stepCase proof ( refl , refl )
        where
            baseCase : (0 ≡ 1 × 0 ≡ 0) → ⊥
            baseCase (() , _)

            stepCase : {m n : ℕ} → ((m ≡ 1) × (n ≡ 0) → ⊥) → ((suc (suc m)) ≡ 1 × (suc n) ≡ 0) → ⊥
            stepCase ih (() , ())

    -- 方法二：构造判别函数 D，利用 ind 消去 isDoubleOf 证明
    -- 这里 D 的模式是完整的：D 0 _ / D (suc _) 0 / D (suc _) (suc _) 覆盖了所有 case
    1isNotDoubleOf0″ : 1 isDoubleOf 0 → ⊥
    1isNotDoubleOf0″ p = ind D tt (λ _ → tt) p
        where
            D : ℕ → ℕ → Set
            D 0 _ = ⊤
            D (suc _) 0 = ⊥
            D (suc _) (suc _) = ⊤

    -- [案例 3] where 子句，外层参数类型 (2 isDoubleOf 0) 是空类型：
    -- D 的模式缺少 (suc zero) 这个 case，但 Agda 不报 missing cases。
    -- 原因：2 isDoubleOf 0 没有任何构造子可以构造（是空类型），
    -- 所以整个函数体（包括 where 子句中的 D）是不可达代码，
    -- 覆盖检查器跳过了 D 的完整性检查。
    --
    -- 从语义上看，_isDoubleOf_ 的结构保证第一个参数永远是偶数（0, 2, 4, ...），
    -- 所以 D (suc zero) _ 在归纳过程中也永远不会被求值。
    2isNotDoubleOf0 : 2 isDoubleOf 0 → ⊥
    2isNotDoubleOf0 p = ind D tt (λ _ → tt) p
        where
            D : ℕ → ℕ → Set
            D 0 _ = ⊤
            -- D (suc zero) _ = ⊥  -- 缺少此 case，但因外层类型为空，不报错
            D (suc (suc _)) 0 = ⊥
            D (suc (suc _)) (suc _) = ⊤

    -- test : ⊤ → Set
    -- test tt = D 0 0
    --   where
    --     D : ℕ → ℕ → Set
    --     D 0 _ = ⊤
    --     D (suc (suc _)) 0 = ⊥
    --     D (suc (suc _)) (suc _) = ⊤
    --     -- 这里应该会报 missing cases

module Single where
    data Odd : ℕ → Set where
        base : Odd 1
        step : {n : ℕ} → Odd n → Odd (suc (suc n))

    Odd9 : Odd 9
    Odd9 = step (step (step (step base)))

    ¬Odd8 : Odd 8 → ⊥
    ¬Odd8 (step (step (step (step ()))))

module Mutual where
    data Even : ℕ → Set
    data Odd : ℕ → Set

    data Even where
        base : Even zero
        step : {n : ℕ} → Odd n → Even (suc n)

    data Odd where
        step : {n : ℕ} → Even n → Odd (suc n)

data _≡_ : ℕ → ℕ → Set where
    base : 0 ≡ 0
    step : {m : ℕ} → {n : ℕ} → m ≡ n → suc m ≡ suc n

data _≢_ : ℕ → ℕ → Set where
    base1 : {n : ℕ} → suc n ≢ zero
    base2 : {n : ℕ} → zero ≢ suc n
    step : {m n : ℕ} → m ≢ n → suc m ≢ suc n
