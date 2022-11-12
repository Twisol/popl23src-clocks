{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Monotonicity where
  open import Data.Nat
    using (ℕ)
  open import Data.Fin
    using (Fin; raise; inject+)
  import Relation.Binary.PropositionalEquality
    as Eq
  open import Function
    using (_∘_)
  open import Data.Product
    using (_,_)

  open import Execution
    using (_→₁_; _⇶_; _⇶₁_)
    using (Event; here; there; now; back)
    using (Trace; id′; _⟫_; _∥_; noop; tick; fork; join; swap)
  open import Causality
    as HB
    using (Ob[_]; event; in-site; out-site)
    using (_↝_; refl; open-interval; left-interval; right-interval; closed-interval)
    using (Arrₙ[_]; Arr₁[_]; ↝ₙ-syntax; ↝₁-syntax)
    using (left; right)
    using (before[_]; after[_]; during[_])
  open import Clock
    as Interpret
    using (Step)

  record Clock {Action State : Type}
               (alg : Step Action State → State)
               (_≤_ : State → State → Type)
             : Type where
    open Step using (act; merge)

    field ≤-refl      : ∀ t → t ≤ t
    field ≤-trans     : ∀ t₁ t₂ t₃ → (t₁ ≤ t₂) → (t₂ ≤ t₃) → (t₁ ≤ t₃)
    field act-mono    : ∀ p t → t ≤ alg (act p t)
    field merge-mono¹ : ∀ t₁ t₂ → t₁ ≤ alg (merge t₁ t₂)
    field merge-mono² : ∀ t₁ t₂ → t₂ ≤ alg (merge t₁ t₂)

  module _ {Action State : Type} {alg : Step Action State → State}
           {_≤_ : State → State → Type} (clock : Clock alg _≤_)
           where
    open Clock clock
      using (≤-refl; ≤-trans; act-mono; merge-mono¹; merge-mono²)

    ≤-reflexive : ∀{s₁ s₂} → (s₁ Eq.≡ s₂) → (s₁ ≤ s₂)
    ≤-reflexive Eq.refl = ≤-refl _

    ⊑₁-syntax : ∀{Γ₁ Γ₂} (step : Γ₁ →₁ Γ₂) → Fin Γ₁ → Fin Γ₂ → Type
    ⊑₁-syntax step s₁ s₂
      = ∀ events input →
        let output = Interpret.atomic alg step events input
        in input s₁ ≤ output s₂
    syntax ⊑₁-syntax step s₁ s₂ = s₁ ⊑₁[ step ] s₂

    ⊑ₙ-syntax : ∀{k Γ₁ Γ₂} (exec : Trace k Γ₁ Γ₂) → Fin Γ₁ → Fin Γ₂ → Type
    ⊑ₙ-syntax exec s₁ s₂
      = ∀ events input →
        let output = Interpret.apply alg exec events input
        in input s₁ ≤ output s₂
    syntax ⊑ₙ-syntax exec s₁ s₂ = s₁ ⊑ₙ[ exec ] s₂

    _⊑_ : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂} → Ob[ exec ] → Ob[ exec ] → Type
    t₁ ⊑ t₂
      = ∀ events input →
        let times = Interpret.timestamp alg events input
        in times t₁ ≤ times t₂

    ⊑ₙ-refl : ∀{Γ} → ∀{t} → t ⊑ₙ[ id′ {Γ} ] t
    ⊑ₙ-refl = λ _ _ → ≤-refl _

    liftˡ : ∀{Γ₁ Γ₂} {step : Γ₁ →₁ Γ₂}
          → ∀{Γ₃ Γ₄} {exec : Γ₃ ⇶₁ Γ₄}
          → {t₃ : Fin Γ₃}
          → {t₄ : Fin Γ₄}
          → t₃ ⊑ₙ[ exec ] t₄
          → raise _ t₃ ⊑ₙ[ step ∥ exec ] raise _ t₄
    liftˡ {Γ₁} {Γ₂} f events input =
      ≤-trans _ _ _
        (f (events ∘ there _) (input ∘ raise _))
        (foo Γ₂ (Interpret.apply alg _ (events ∘ there _) (input ∘ raise Γ₁)))
      where
        foo : ∀ Γ₁  {f : Fin Γ₁ → State}
            → ∀{Γ₂} (g : Fin Γ₂ → State)
            → ∀{t}
            → g t ≤ Interpret.par alg f g (raise Γ₁ t)
        foo ℕ.zero     {f} _ = ≤-refl _
        foo (ℕ.suc Γ₁) {f} _ = foo Γ₁ {f ∘ Fin.suc} _

    liftʳ : ∀{Γ₁ Γ₂} {step : Γ₁ →₁ Γ₂}
          → ∀{Γ₃ Γ₄} {exec : Γ₃ ⇶₁ Γ₄}
          → {t₁ : Fin Γ₁}
          → {t₂ : Fin Γ₂}
          → t₁ ⊑₁[ step ] t₂
          → inject+ _ t₁ ⊑ₙ[ step ∥ exec ] inject+ _ t₂
    liftʳ f events input
      = ≤-trans _ _ _
          (f (events ∘ here _) (input ∘ inject+ _))
          (foo (Interpret.atomic alg _ (events ∘ here _) (input ∘ inject+ _)) _)
      where
        foo : ∀{Γ₁} → (f : Fin Γ₁ → State)
            → ∀{Γ₂} → {g : Fin Γ₂ → State}
            → ∀ t
            → f t ≤ Interpret.par alg f g (inject+ Γ₂ t)
        foo f Fin.zero    = ≤-refl _
        foo f (Fin.suc t) = foo (f ∘ Fin.suc) t

    _;_ : ∀{Γ₁ Γᵢ Γ₂} {exec : Γ₁ ⇶ Γᵢ} {step : Γᵢ ⇶₁ Γ₂}
        → {t₁ : Fin Γ₁}
        → {tᵢ : Fin Γᵢ}
        → {t₂ : Fin Γ₂}
        → t₁ ⊑ₙ[ exec ] tᵢ
        → tᵢ ⊑ₙ[ step ] t₂
        → t₁ ⊑ₙ[ exec ⟫ step ] t₂
    (f ; g) events input
      = ≤-trans _ _ _
          (f (events ∘ back _) input)
          (g (events ∘ now _) (Interpret.apply alg _ (events ∘ back _) input))

    atomic-mono : ∀{Γ₁ Γ₂} (step : Γ₁ →₁ Γ₂)
                → (t₁ : Fin Γ₁)
                → (t₂ : Fin Γ₂)
                → t₁ ↝₁[ step ] t₂
                → t₁ ⊑₁[ step ] t₂
    (atomic-mono noop Fin.zero Fin.zero _) _ _
      = ≤-refl _
    (atomic-mono tick Fin.zero Fin.zero _) events inputs
      = act-mono (events _) (inputs (Fin.zero))
    (atomic-mono fork Fin.zero Fin.zero _ _) _
      = ≤-refl _
    (atomic-mono fork Fin.zero (Fin.suc Fin.zero) _ _) _
      = ≤-refl _
    (atomic-mono join Fin.zero Fin.zero _) _ input
      = merge-mono¹ (input Fin.zero) (input (Fin.suc Fin.zero))
    (atomic-mono join (Fin.suc Fin.zero) Fin.zero _) _ input
      = merge-mono² (input Fin.zero) (input (Fin.suc Fin.zero))
    (atomic-mono swap Fin.zero _ Eq.refl) _ _
      = ≤-refl _
    (atomic-mono swap (Fin.suc Fin.zero) _ Eq.refl) _ _
      = ≤-refl _

    apply-mono : ∀{k Γ₁ Γ₂} (exec : Trace k Γ₁ Γ₂)
               → {t₁ : Fin Γ₁}
               → {t₂ : Fin Γ₂}
               → t₁ ↝ₙ[ exec ] t₂
               → t₁ ⊑ₙ[ exec ] t₂
    apply-mono id′ Eq.refl
      = ⊑ₙ-refl
    apply-mono (_ ∥ exec) (right _ _ t₁↝t₂)
      = liftˡ (apply-mono exec t₁↝t₂)
    apply-mono (step ∥ _) (left _ _ t₁↝t₂)
      = liftʳ (atomic-mono step _ _ t₁↝t₂)
    apply-mono (exec ⟫ step) (_ , t₁↝tᵢ , tᵢ↝t₂)
      = apply-mono exec t₁↝tᵢ ; apply-mono step tᵢ↝t₂

    foo : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
        → (t : Ob[ exec ])
        → ∀ events inputs
        → Interpret.apply alg HB.after-ob[ t ] (events ∘ HB.lift-obʳ t)
            (Interpret.apply alg HB.before-ob[ t ] (events ∘ HB.lift-obˡ t)
              inputs)
        Eq.≡ Interpret.apply alg exec events inputs
    foo (in-site x) events inputs = Eq.refl
    foo (out-site x) events inputs = Eq.refl
    foo (event (now prefix x)) events inputs = Eq.refl
    foo (event (back step x)) events inputs
      = Eq.cong (Interpret.apply alg step (events ∘ now _))
          (foo (event x) (events ∘ back _) inputs)

    bar : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
        → {t₁ t₂ : Ob[ exec ]}
        → (t₁≤t₂ : t₁ HB.≤ t₂)
        → ∀ events inputs
        → Interpret.apply alg HB.during[ t₁≤t₂ ] (events ∘ HB.lift t₁≤t₂)
            (Interpret.apply alg HB.before[ t₁≤t₂ ] (events ∘ HB.liftˡ t₁≤t₂)
              inputs)
        Eq.≡ Interpret.apply alg HB.before-ob[ t₂ ] (events ∘ HB.lift-obˡ t₂) inputs
    bar (refl _) events inputs = Eq.refl
    bar (open-interval t₁ t₂) events inputs = Eq.refl
    bar (left-interval t₁ t₂) events inputs = Eq.refl
    bar (right-interval (back step t₁) t₂) events inputs
      = Eq.cong (Interpret.apply alg step (events ∘ now _))
          (foo (event t₁) (events ∘ back _) inputs)
    bar (right-interval (now prefix t₁) t₂) events inputs = Eq.refl
    bar (closed-interval (HB.init ev₁ ev₂)) events inputs
      = Eq.cong (Interpret.apply alg _ (events ∘ now _))
        (foo (event ev₁) (events ∘ back _) inputs)
    bar (closed-interval (HB.go {ev₁ = t₁} {t₂} st t₁<t₂)) events inputs
      = bar (closed-interval t₁<t₂) (events ∘ back _) inputs

    timestamp-mono : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
                   → {t₁ t₂ : Ob[ exec ]}
                   → t₁ ↝ t₂
                   → t₁ ⊑ t₂
    timestamp-mono {_} {_} {_} {t₁} {t₂} (t₁≤t₂ , t₁↝t₂) events inputs
      = let ins = Interpret.apply alg before[ t₁≤t₂ ] (events ∘ HB.liftˡ t₁≤t₂) inputs
        in ≤-trans _ _ _
             (apply-mono during[ t₁≤t₂ ] t₁↝t₂ (events ∘ HB.lift t₁≤t₂) ins)
             (≤-reflexive (Eq.cong (λ z → z HB.site[ t₂ ]) (bar t₁≤t₂ events inputs)))
