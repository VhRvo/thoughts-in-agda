module VecHeadElim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- open import Data.Nat.Properties using (zero≢suc)

------------------------------------------------------------------------
-- 一个显式写出来的 Vec eliminator（依赖消去）
------------------------------------------------------------------------

Vec-elim
  : ∀ {A : Set}
    {P : ∀ {n : ℕ} → Vec A n → Set}
  → P []
  → (∀ {n} (x : A) (xs : Vec A n) → P xs → P (x ∷ xs))
  → ∀ {n} (xs : Vec A n) → P xs
Vec-elim p[] p∷ []       = p[]
Vec-elim p[] p∷ (x ∷ xs) = p∷ x xs (Vec-elim p[] p∷ xs)

------------------------------------------------------------------------
-- 版本 1：unit motive 版本
-- 关键：motive 依赖长度 n：n=0 时返回 ⊤，n=suc _ 时返回 A
-- 所以 [] 分支只需要给 tt，且对 Vec A (suc n) 的调用永远走不到它。
------------------------------------------------------------------------

headᵤ : ∀ {A : Set} {n : ℕ} → Vec A (suc n) → A
headᵤ {A} {n} v =
  Vec-elim {A = A} {P = P}
    tt
    (λ {n} x xs ih → x)
    v
  where
    P : ∀ {m : ℕ} → Vec A m → Set
    P {zero}  _ = ⊤
    P {suc m} _ = A

------------------------------------------------------------------------
-- 版本 2：noConfusion/False.elim 风格
-- 思路：强行让返回类型在所有长度上都是 A（不随 n 变），那么 [] 分支必须产出 A。
-- 但我们额外带一个等式证明 n ≡ suc m：
--   - 在 [] 分支里 n = 0，于是得到 0 ≡ suc m，借助 zero≢suc 推出 ⊥，再 ⊥-elim 得到 A
--   - 在 (x ∷ xs) 分支里，匹配 p = refl（等价于“noConfusion 成功”），直接返回 x
------------------------------------------------------------------------

zero≢suc : ∀ (m : ℕ) → zero ≡ suc m → ⊥
zero≢suc m ()

head⊥-helper : ∀ {A : Set} {n m : ℕ} → Vec A n → n ≡ suc m → A
head⊥-helper []       p    = ⊥-elim (zero≢suc _ p)
head⊥-helper (x ∷ xs) refl = x

head⊥ : ∀ {A : Set} {n : ℕ} → Vec A (suc n) → A
head⊥ v = head⊥-helper v refl
