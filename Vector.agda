{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
open import Relation.Nullary
  using (Dec)
open import Relation.Binary.PropositionalEquality
  using (_≡_)

module Vector (Pid : Type) (_≟_ : (p₁ p₂ : Pid) → Dec (p₁ ≡ p₂)) where
  open import Data.Bool
    using (true; false)
  open import Data.Nat
    using (ℕ; _+_; _⊔_; _≤_)
  open import Data.Fin
    using (Fin)
  open import Data.Nat.Properties
    as ℕ-Prop
    using ()
  open import Data.Bool
    using (if_then_else_)
  open import Relation.Nullary
    using (does; _because_)

  open import Execution
    using (_⇶_; Event)
  open import Causality
    using (Ob[_]; _↝_)
  open import Clock
    as Interpret
    using (Step; act; merge)
  open import Monotonicity
    using (Clock; apply-mono)
  open Clock
    using (≤-refl; ≤-trans; act-mono; merge-mono¹; merge-mono²)

  -- If Pid ≃ Fin n, then Time ≃ Vec n Scalar.Time.
  -- But the exponential formulation doesn't bake in any questions of size at the ground floor.
  Time : Type
  Time = Pid → ℕ

  _⊑_ : Time → Time → Type
  t₁ ⊑ t₂ = ∀ s → t₁ s ≤ t₂ s

  alg : Step Pid Time → Time
  alg (act at t) s
    = if does (at ≟ s)
        then (1 + t s)
        else t s
  alg (merge t₁ t₂) s
    = t₁ s ⊔ t₂ s

  clock : Clock alg _⊑_
  (≤-refl clock) _ _ = ℕ-Prop.≤-refl
  (≤-trans clock) _ _ _ t₁≤t₂ t₂≤t₃ s = ℕ-Prop.≤-trans (t₁≤t₂ s) (t₂≤t₃ s)
  (act-mono clock) at _ s with at ≟ s
  ... | false because _ = ℕ-Prop.≤-refl
  ... | true  because _ = ℕ-Prop.≤-step ℕ-Prop.≤-refl
  (merge-mono¹ clock) _ _ _ = ℕ-Prop.m≤m⊔n _ _
  (merge-mono² clock) _ _ _ = ℕ-Prop.m≤n⊔m _ _

  timestamp : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
            → (events : Event exec → Pid)
            → (input : Fin Γ₁ → Time)
            → (Ob[ exec ] → Time)
  timestamp = Interpret.timestamp alg

  mono : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Ob[ exec ]}
       → t₁ ↝ t₂
       → ∀ events input
       → timestamp events input t₁ ⊑ timestamp events input t₂
  mono = Monotonicity.timestamp-mono clock
