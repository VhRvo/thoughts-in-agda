{-# OPTIONS --show-implicit #-}
{-# OPTIONS --show-irrelevant #-}

module Agda.Absurd where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_; returnTC to return)
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Nat

data ⊥ : Set where

myAbsurd : false ≡ true → ⊥
myAbsurd ()

-- 直接 quote Definition 并显示
macro
  showDef : Name → Term → TC ⊤
  showDef n hole = do
    d ← getDefinition n
    qdef ← quoteTC d
    typeError (strErr "Definition of " ∷ nameErr n ∷ strErr ":\n" ∷ termErr qdef ∷ [])

-- 对比: 一个正常的函数 (有 body)
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- 另一个对比: 正常的 identity 函数
myId : {A : Set} → A → A
myId x = x

-- 这会触发错误并显示内部定义
-- test1 : ⊤
-- test1 = showDef myAbsurd

-- test3 : ⊤
-- test3 = showDef myId
