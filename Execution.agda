{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Execution where
  open import Data.Nat
    using (ℕ; zero; suc; _+_)
  open import Data.Fin
    using (Fin; #_)
  open import Data.Fin.Permutation
    using (Permutation)

  infix   5 _→₁_ _⇶₁_ _⇶_  -- under _+_ at 6
  infixl 15 _⟫_ _⟫′_
  infixr 20 _∥_

  data _→₁_ : ℕ → ℕ → Type where
    -- 0 ─── 0
    noop : 1 →₁ 1

    -- 0 ─⋆─ 0
    tick : 1 →₁ 1

    --    ┌─ 0
    -- 0 ─┤
    --    └─ 1
    fork : 1 →₁ 2

    -- 0 ─┐
    --    ├─ 0
    -- 1 ─┘
    join : 2 →₁ 1

    -- 0 ─╥─ 0
    --    ║
    -- 1 ─╨─ 1
    swap : 2 →₁ 2

  data Layer : Type where
    Par Seq : Layer

  data Trace : Layer → ℕ → ℕ → Type where
    empty : Trace Par 0 0

    _∥_ : ∀{x y} → (x →₁ y)
        → ∀{a b} → Trace Par a b
        → Trace Par (x + a) (y + b)

    id′ : ∀{a} → Trace Seq a a

    _⟫_ : ∀{Γ₁ Γ₂} (prefix : Trace Seq Γ₁ Γ₂)
        → ∀{Γ₃} (step : Trace Par Γ₂ Γ₃)
        → Trace Seq Γ₁ Γ₃

  _⇶₁_ = Trace Par
  _⇶_  = Trace Seq


  id : ∀ k Γ → Trace k Γ Γ
  id Par zero = empty
  id Par (suc Γ₃) = noop ∥ id Par Γ₃
  id Seq Γ = id′

  _⟫′_ : ∀{Γ₁ Γ₂ Γ₃} → (Γ₁ ⇶ Γ₂) → (Γ₂ ⇶ Γ₃) → (Γ₁ ⇶ Γ₃)
  prefix ⟫′ id′ = prefix
  prefix ⟫′ (suffix ⟫ step) = (prefix ⟫′ suffix) ⟫ step

  _∥′_ : ∀{x y} → (x ⇶₁ y)
       → ∀{a b} → (a ⇶₁ b)
       → (x + a ⇶₁ y + b)
  empty         ∥′ right =                 right
  (noop ∥ left) ∥′ right = noop ∥ (left ∥′ right)
  (tick ∥ left) ∥′ right = tick ∥ (left ∥′ right)
  (fork ∥ left) ∥′ right = fork ∥ (left ∥′ right)
  (join ∥ left) ∥′ right = join ∥ (left ∥′ right)
  (swap ∥ left) ∥′ right = swap ∥ (left ∥′ right)

  _⊗_ : ∀{Γ₁ Γ₂} → (Γ₁ ⇶ Γ₂)
      → ∀{Γ₃ Γ₄} → (Γ₃ ⇶ Γ₄)
      → (Γ₁ + Γ₃ ⇶ Γ₂ + Γ₄)
  id′               ⊗ id′               = id′
  id′               ⊗ (prefix₂ ⟫ step₂) = (id′     ⊗ prefix₂) ⟫ (id _ _ ∥′ step₂)
  (prefix₁ ⟫ step₁) ⊗ id′               = (prefix₁ ⊗ id′    ) ⟫ (step₁  ∥′ id _ _)
  (prefix₁ ⟫ step₁) ⊗ (prefix₂ ⟫ step₂) = (prefix₁ ⊗ prefix₂) ⟫ (step₁  ∥′ step₂)

  whiskerʳ : ∀{k Γ₁ Γ₂} → Trace k Γ₁ Γ₂ → ∀ Γ → Trace k (Γ₁ + Γ) (Γ₂ + Γ)
  whiskerʳ {Par} exec Γ = exec ∥′ id _ Γ
  whiskerʳ {Seq} exec Γ = exec ⊗  id _ Γ

  whiskerˡ : ∀{k} Γ {Γ₁ Γ₂} → Trace k Γ₁ Γ₂ → Trace k (Γ + Γ₁) (Γ + Γ₂)
  whiskerˡ {Par} Γ exec = id _ Γ ∥′ exec
  whiskerˡ {Seq} Γ exec = id _ Γ ⊗  exec

  private module Example-Diagram where
    infixr 16 start_
    start_ : ∀{a b} → Trace Par a b → Trace Seq a b
    start_ = id′ ⟫_

    -- #0 │         │ #1
    --    a         d
    --    ├───┐ ┌───┤  |
    --    b   ╞═╡   e  |
    --    ├───┘ └───┤  v
    --    c         f
    -- #0 │         │ #1
    exec : 2 ⇶ 2
    exec =
      start tick     ∥    tick ∥ empty
      ⟫         fork ∥ fork    ∥ empty
      ⟫     tick ∥ swap ∥ tick ∥ empty
      ⟫         join ∥ join    ∥ empty
      ⟫     tick     ∥    tick ∥ empty

    -- And now for something completely ridiculous!

    helper : ∀{x y}
           → x →₁ y
           → ∀{a b}
           → a ⇶₁ b
           → (x Data.Nat.+ a) ⇶₁ (y Data.Nat.+ b)
    helper = _∥_

    ⋆_ = helper tick

    │_ = helper noop
    └─┐_ = │_
    └───┐_ = │_
    └─────┐_ = │_
    ┌─┘_ = │_
    ┌───┘_ = │_
    ┌─────┘_ = │_

    └─┬─┘_ = helper join
    └─┤_ = └─┬─┘_
    └───┤_ = └─┬─┘_
    └─────┤_ = └─┬─┘_
    ├─┘_ = └─┬─┘_
    ├───┘_ = └─┬─┘_
    ├─────┘_ = └─┬─┘_

    ┌─┴─┐_ = helper fork
    ├─┐_ = ┌─┴─┐_
    ├───┐_ = ┌─┴─┐_
    ├─────┐_ = ┌─┴─┐_
    ┌─┤_ = ┌─┴─┐_
    ┌───┤_ = ┌─┴─┐_
    ┌─────┤_ = ┌─┴─┐_

    ╞═╡_ = helper swap
    ╞═══╡_ = ╞═╡_
    ╞═════╡_ = ╞═╡_

    exec' : 2 ⇶ 2
    exec' =
      start │         │ empty
      ⟫     a         d empty
      ⟫     ├───┐ ┌───┤ empty
      ⟫     b   ╞═╡   e empty
      ⟫     ├───┘ └───┤ empty
      ⟫     c         f empty
      ⟫     │         │ empty
      where
        a_ = ⋆_
        b_ = ⋆_
        c_ = ⋆_
        d_ = ⋆_
        e_ = ⋆_
        f_ = ⋆_

  data Event₁ : ∀{Γ₁ Γ₂} → (Γ₁ →₁ Γ₂) → Type where
    event : Event₁ tick

  data Event : ∀{k Γ₁ Γ₂} → (Trace k Γ₁ Γ₂) → Type where
    here : ∀{Γ₁ Γ₂} {step : Γ₁ →₁ Γ₂}
         → ∀{Γ₃ Γ₄} (right : Γ₃ ⇶₁ Γ₄)
         → Event₁ step
         → Event (step ∥ right)
    there : ∀{Γ₁ Γ₂} (step : Γ₁ →₁ Γ₂)
          → ∀{Γ₃ Γ₄} {right : Γ₃ ⇶₁ Γ₄}
          → Event right
          → Event (step ∥ right)

    now : ∀{Γ₁ Γ₂} (prefix : Γ₁ ⇶ Γ₂)
        → ∀{Γ₃} {step : Γ₂ ⇶₁ Γ₃}
        → Event step
        → Event (prefix ⟫ step)
    back : ∀{Γ₁ Γ₂} {prefix : Γ₁ ⇶ Γ₂}
         → ∀{Γ₃} (step : Γ₂ ⇶₁ Γ₃)
         → Event prefix
         → Event (prefix ⟫ step)

  private module Example-Events where
    -- #0 │         │ #1
    --    a         d
    --    ├───┐ ┌───┤  |
    --    b   ╞═╡   e  |
    --    ├───┘ └───┤  v
    --    c         f
    -- #0 │         │ #1
    exec = Example-Diagram.exec

    c : Event exec
    c = now _ (here _ event)

    e : Event exec
    e = back _ (back _ (now _ (there _ (there _ (here _ event)))))
