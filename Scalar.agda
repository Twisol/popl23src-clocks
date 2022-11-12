{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Scalar (Pid : Type) where
  open import Data.Nat
    using (ℕ; _+_; _⊔_; _≤_)
  open import Data.Nat.Properties
    as ℕ-Prop
    using ()
  open import Clock
    as Interpret
    using (Step; act; merge)
  open import Monotonicity
    using (Clock; apply-mono)
  open Clock
    using (≤-refl; ≤-trans; act-mono; merge-mono¹; merge-mono²)

  alg : Step Pid ℕ → ℕ
  alg (act   _  t ) = 1 + t
  alg (merge t₁ t₂) = t₁ ⊔ t₂

  clock : Clock alg _≤_
  (≤-refl clock) _ = ℕ-Prop.≤-refl
  (≤-trans clock) _ _ _ = ℕ-Prop.≤-trans
  (act-mono clock) _ _ = ℕ-Prop.≤-step ℕ-Prop.≤-refl
  (merge-mono¹ clock) = ℕ-Prop.m≤m⊔n
  (merge-mono² clock) = ℕ-Prop.m≤n⊔m

  timestamp = Interpret.timestamp alg

  mono = Monotonicity.timestamp-mono clock
