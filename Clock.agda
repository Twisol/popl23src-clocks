{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Clock where
  open import Function
    using (_∘_)
  open import Data.Fin
    using (Fin)
  open import Data.Nat
    using (ℕ; _+_)
  open import Execution
    using (_→₁_; noop; tick; fork; join; swap)
    using (Trace; _⇶_; _⇶₁_; empty; id′; _∥_; _⟫_)
    using (Event₁; event; Event; here; there; now; back)
  open import Causality
    as HB
    using (Ob[_]; event)

  data Step (Action State : Type) : Type where
    act   : Action → State → Step Action State
    merge : State  → State → Step Action State

  -- Given an algebra on steps, we can specify computations
  -- on replicas across spatially-distributed sites.
  module _ {Action State : Type} (alg : Step Action State → State) where
    Valuation : ℕ → Type
    Valuation Γ = Fin Γ → State

    par : ∀{Γ₁} → Valuation Γ₁
        → ∀{Γ₂} → Valuation Γ₂
        → Valuation (Γ₁ + Γ₂)
    par {ℕ.zero} f g = g
    par {ℕ.suc Γ₁} f g Fin.zero = f Fin.zero
    par {ℕ.suc Γ₁} f g (Fin.suc s) = par (f ∘ Fin.suc) g s

    left : ∀{Γ₁ Γ₂} → Valuation (Γ₁ + Γ₂) → Valuation Γ₁
    left f = f ∘ Data.Fin.inject+ _

    right : ∀{Γ₁ Γ₂} → Valuation (Γ₁ + Γ₂) → Valuation Γ₂
    right f = f ∘ Data.Fin.raise _

    _⊗_ : ∀{Γ₁ Γ₂} → (Valuation Γ₁ → Valuation Γ₂)
        → ∀{Γ₃ Γ₄} → (Valuation Γ₃ → Valuation Γ₄)
        → (Valuation (Γ₁ + Γ₃) → Valuation (Γ₂ + Γ₄))
    _⊗_ f g ins = par (f (left ins)) (g (right ins))

    atomic : ∀{Γ₁ Γ₂} (step : Γ₁ →₁ Γ₂)
           → (Event₁ step → Action)
           → Valuation Γ₁ → Valuation Γ₂
    atomic noop evs f = f
    atomic swap evs f = f ∘ Data.Fin.opposite
    atomic fork evs f = f ∘ Function.const Fin.zero      -- assuming `merge x x ≡ x`
    atomic join evs f = alg ∘ merge (f Fin.zero) ∘ f ∘ Fin.suc
    atomic tick evs f = alg ∘ act (evs event) ∘ f

    apply : ∀{Γ₁ Γ₂ k} (exec : Trace k Γ₁ Γ₂) (evs : Event exec → Action)
          → Valuation Γ₁ → Valuation Γ₂
    apply empty evs = Function.id
    apply id′   evs = Function.id
    apply (step ∥ exec) evs = atomic step (evs ∘ here _) ⊗ apply exec (evs ∘ there _)
    apply (exec ⟫ step) evs = apply  step (evs ∘ now  _) ∘ apply exec (evs ∘ back  _)

    timestamp : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
              → (Event exec → Action)
              → Valuation Γ₁
              → (Ob[ exec ] → State)
    timestamp evs ins t = apply HB.before-ob[ t ] (evs ∘ HB.lift-obˡ t) ins HB.site[ t ]

    -- Relabel the events of an execution
    relabel : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
            → (Event exec → Action)
            → (Event exec → (Valuation Γ₁ → State))
    relabel evs ev ins = timestamp evs ins (event ev)
