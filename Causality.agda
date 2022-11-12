{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Causality where
  open import Function
    using ()
  open import Data.Unit
    using (⊤)
  open import Data.Empty
    using (⊥)
  open import Data.Product
    using (Σ-syntax)
  open import Data.Nat
    using (ℕ; _+_)
  open import Data.Fin
    using (Fin; opposite; inject+; raise)
  open import Relation.Binary.Construct.Composition
    using (_;_)
  open import Relation.Binary.PropositionalEquality
    using (_≡_)
  open import Execution
    using (Trace; empty; id′; _∥_; _⟫_; _→₁_; _⇶₁_; _⇶_; id)
    using (noop; tick; fork; join; swap)
    using (Event₁; event; Event; here; there; now; back)

  data Ob[_] {k Γ₁ Γ₂} (exec : Trace k Γ₁ Γ₂) : Type where
    -- Input sites entering the execution.
    in-site  : Fin Γ₁     → Ob[ exec ]
    -- Output sites exiting the execution.
    out-site : Fin Γ₂     → Ob[ exec ]
    -- Internal nodes of the execution.
    event    : Event exec → Ob[ exec ]

  data _<_ {Γ₁ Γ₂} : ∀{k} {exec : Trace k Γ₁ Γ₂} (_ _ : Event exec) → Type where
    init : ∀{Γᵢ} {prefix : Γ₁ ⇶ Γᵢ} {step : Γᵢ ⇶₁ Γ₂}
         → (ev₁ : Event prefix)
         → (ev₂ : Event step)
         → back step ev₁ < now prefix ev₂

    go : ∀{Γᵢ} {prefix : Γ₁ ⇶ Γᵢ}
       → {ev₁ ev₂ : Event prefix}
       → (st : Γᵢ ⇶₁ Γ₂)
       → ev₁ < ev₂
       → back st ev₁ < back st ev₂

  data _≤_ {k Γ₁ Γ₂} {exec : Trace k Γ₁ Γ₂} : (_ _ : Ob[ exec ]) → Type where
    refl : (t : Ob[ exec ])
         → t ≤ t

    open-interval : (s₁ : Fin Γ₁)
                  → (s₂ : Fin Γ₂)
                  → in-site s₁ ≤ out-site s₂

    left-interval : (s₁ : Fin Γ₁)
                  → (t₂ : Event exec)
                  → in-site s₁ ≤ event t₂

    right-interval : (t₁ : Event exec)
                   → (s₂ : Fin Γ₂)
                   → event t₁ ≤ out-site s₂

    closed-interval : {t₁ t₂ : Event exec}
                    → (t₁<t₂ : t₁ < t₂)
                    → event t₁ ≤ event t₂


  _<∘_ : ∀{k Γ₁ Γ₂} {exec : Trace k Γ₁ Γ₂} {ev₁ ev₂ ev₃ : Event exec}
       → (ev₁ < ev₂) → (ev₂ < ev₃) → (ev₁ < ev₃)
  go _ _       <∘ init _ _       = init _ _
  go _ ev₁≤ev₂ <∘ go   _ ev₂≤ev₃ = go   _ (ev₁≤ev₂ <∘ ev₂≤ev₃)

  _≤∘_ : ∀{k Γ₁ Γ₂} {exec : Trace k Γ₁ Γ₂} {t₁ t₂ t₃ : Ob[ exec ]}
       → (t₁ ≤ t₂) → (t₂ ≤ t₃) → (t₁ ≤ t₃)
  t₁ ≤∘ refl _ = t₁
  refl            _     ≤∘ open-interval   _ _   = open-interval   _ _
  refl            _     ≤∘ left-interval   _ _   = left-interval   _ _
  refl            _     ≤∘ right-interval  _ _   = right-interval  _ _
  left-interval   _ _   ≤∘ right-interval  _ _   = open-interval   _ _
  closed-interval _     ≤∘ right-interval  _ _   = right-interval  _ _
  refl            _     ≤∘ closed-interval t₁<t₂ = closed-interval t₁<t₂
  left-interval   _ _   ≤∘ closed-interval _     = left-interval   _ _
  closed-interval t₁<tᵢ ≤∘ closed-interval tᵢ<t₂ = closed-interval (t₁<tᵢ <∘ tᵢ<t₂)

  cut[_] : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂} → Ob[ exec ] → ℕ
  cut[_] {Γ₁ = Γ₁} (in-site _ )        = Γ₁
  cut[_] {Γ₂ = Γ₂} (out-site _)        = Γ₂
  cut[_] {Γ₂ = Γ₂} (event (now _ _))   = Γ₂
  cut[_]           (event (back _ ev)) = cut[ event ev ]

  site[_] : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
          → (t : Ob[ exec ]) → Fin cut[ t ]
  site[ in-site x ] = x
  site[ out-site x ] = x
  site[ event (back _ x) ] = site[ event x ]
  site[ event (now  _ x) ] = site'[ x ]
    where
      site'[_] : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶₁ Γ₂}
               → Event exec → Fin Γ₂
      site'[ here right event ] = Fin.zero
      site'[ there noop ev ] = Fin.suc site'[ ev ]
      site'[ there tick ev ] = Fin.suc site'[ ev ]
      site'[ there fork ev ] = Fin.suc (Fin.suc site'[ ev ])
      site'[ there join ev ] = Fin.suc site'[ ev ]
      site'[ there swap ev ] = Fin.suc (Fin.suc site'[ ev ])

  before-ob[_] : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
               → (t : Ob[ exec ]) → (Γ₁ ⇶ cut[ t ])
  before-ob[_] {_} {_} {_}    (in-site  _) = id _ _
  before-ob[_] {_} {_} {exec} (out-site _) = exec
  before-ob[_] {_} {_} {_} (event (now prefix {step = step} e)) = prefix ⟫ step
  before-ob[_] {_} {_} {_} (event (back step e)) = before-ob[_] (event e)

  after-ob[_] : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
              → (t : Ob[ exec ]) → cut[ t ] ⇶ Γ₂
  after-ob[_] {exec = exec} (in-site _) = exec
  after-ob[ out-site _ ] = id _ _
  after-ob[ event (now prefix ev) ] = id _ _
  after-ob[ event (back step ev) ] = after-ob[ event ev ] ⟫ step


  before[_] : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Ob[ exec ]}
            → (t₁ ≤ t₂)
            → Γ₁ ⇶ cut[ t₁ ]
  before[_] {t₁ = t₁} _ = before-ob[ t₁ ]

  after[_] : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Ob[ exec ]}
           → (t₁ ≤ t₂)
           → cut[ t₂ ] ⇶ Γ₂
  after[_] {t₂ = t₂} _ = after-ob[ t₂ ]

  during[_] : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Ob[ exec ]}
            → (t₁ ≤ t₂)
            → cut[ t₁ ] ⇶ cut[ t₂ ]
  during[ refl _ ] = id _ _
  during[_] {exec = exec} (open-interval t₁ t₂) = exec
  during[ left-interval  _ t₂ ] = before[ refl (event t₂) ]
  during[ right-interval t₁ _ ] = after[  refl (event t₁) ]
  during[ closed-interval (init {step = step} ev₁ _) ] = after[ refl (event (back step ev₁)) ]
  during[ closed-interval (go _ t₁<t₂) ] = during[ closed-interval t₁<t₂ ]


  lift-obˡ : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
           → (pivot : Ob[ exec ])
           → (Event before-ob[ pivot ] → Event exec)
  lift-obˡ (out-site _) ev = ev
  lift-obˡ (event (now prefix t₂)) ev = ev
  lift-obˡ (event (back step t₂)) ev = back _ (lift-obˡ (event t₂) ev)

  lift-obʳ : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
           → (pivot : Ob[ exec ])
           → (Event after-ob[ pivot ] → Event exec)
  lift-obʳ (in-site _) ev = ev
  lift-obʳ (event (back _ _))     (now  _ ev) = now _ ev
  lift-obʳ (event (back _ pivot)) (back _ ev) = back _ (lift-obʳ (event pivot) ev)

  liftˡ : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
        → {t₁ t₂ : Ob[ exec ]}
        → (t₁≤t₂ : t₁ ≤ t₂)
        → (Event before[ t₁≤t₂ ] → Event exec)
  liftˡ {t₁ = t₁} _ = lift-obˡ t₁

  liftʳ : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
        → {t₁ t₂ : Ob[ exec ]}
        → (t₁≤t₂ : t₁ ≤ t₂)
        → (Event after[ t₁≤t₂ ] → Event exec)
  liftʳ {t₂ = t₂} _ = lift-obʳ t₂

  lift : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂}
       → {t₁ t₂ : Ob[ exec ]}
       → (t₁≤t₂ : t₁ ≤ t₂)
       → (Event during[ t₁≤t₂ ] → Event exec)
  lift (open-interval _ _) ev = ev
  lift (left-interval _ t₂) ev = lift-obˡ (event t₂) ev
  lift (right-interval t₁ t₂) ev = lift-obʳ (event t₁) ev
  lift (closed-interval (init t₁ _)) ev = lift-obʳ (event (back _ t₁)) ev
  lift (closed-interval (go st t₁≤t₂)) ev = back _ (lift (closed-interval t₁≤t₂) ev)

  Arr₁[_] : ∀{x y} → (x →₁ y) → (Fin x → Fin y → Type)
  Arr₁[ noop ] _ _ = ⊤
  Arr₁[ tick ] _ _ = ⊤
  Arr₁[ fork ] _ _ = ⊤
  Arr₁[ join ] _ _ = ⊤
  Arr₁[ swap ] a b = (b ≡ opposite a)

  data _⊗_ {Γ₁ Γ₂} (f : Fin Γ₁ → Fin Γ₂ → Type)
           {Γ₃ Γ₄} (g : Fin Γ₃ → Fin Γ₄ → Type)
         : Fin (Γ₁ + Γ₃) → Fin (Γ₂ + Γ₄) → Type where
    left : ∀ a b
         → (f a b)
         → (f ⊗ g) (inject+ Γ₃ a) (inject+ Γ₄ b)

    right : ∀ a b
          → (g a b)
          → (f ⊗ g) (raise Γ₁ a) (raise Γ₂ b)

  Arrₙ[_] : ∀{k Γ₁ Γ₂} → Trace k Γ₁ Γ₂ → (Fin Γ₁ → Fin Γ₂ → Type)
  Arrₙ[ empty ]       = _≡_
  Arrₙ[ id′ ]         = _≡_
  Arrₙ[ step ∥ exec ] = Arr₁[ step ] ⊗ Arrₙ[ exec ]
  Arrₙ[ exec ⟫ step ] = Arrₙ[ exec ] ; Arrₙ[ step ]

  Arr[_] : ∀{Γ₁ Γ₂} (exec : Γ₁ ⇶ Γ₂) (_ _ : Ob[ exec ]) → Type
  Arr[ exec ] t₁ t₂
    = Σ[ t₁≤t₂ ∈ t₁ ≤ t₂ ]
        Arrₙ[ during[ t₁≤t₂ ] ] site[ t₁ ] site[ t₂ ]

  ↝₁-syntax = Arr₁[_]
  syntax ↝₁-syntax exec t₁ t₂ = t₁ ↝₁[ exec ] t₂

  ↝ₙ-syntax = Arrₙ[_]
  syntax ↝ₙ-syntax exec t₁ t₂ = t₁ ↝ₙ[ exec ] t₂

  _↝_ : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂} → (_ _ : Ob[ exec ]) → Type
  ob₁ ↝ ob₂ = Arr[ _ ] ob₁ ob₂

  start[_] : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Ob[ exec ]} → (t₁ ↝ t₂) → Ob[ exec ]
  start[_] {t₁ = t₁} _ = t₁

  end[_] : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Ob[ exec ]} → (t₁ ↝ t₂) → Ob[ exec ]
  end[_] {t₂ = t₂} _ = t₂
