module ReusableDeBrujinSyntax (Type : Set) where

open import Data.List hiding (drop; all)

Context : Set
Context = List Type

-- Typed de Brujin indexes. `this` is the leftmost variable in the context,
-- `that this` the second, and so on. You can read values as natural numbers,
-- but they carry more information -- a Var Γ τ is both a variable and a proof
-- that it is valid in the given context.
data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ ∷ Γ) τ
  that : ∀ {σ Γ τ} → Var Γ τ → Var (σ ∷ Γ) τ

-- Let's generalize weakening, so that we can weaken a term to any bigger context.
-- So first let's define "bigger context".

infix 4 _≼_
data _≼_ : (Γ₁ Γ₂ : Context) → Set where
  ∅ : [] ≼ []
  keep : ∀ {Γ₁ Γ₂} → (τ : Type) →
         Γ₁ ≼ Γ₂ →
         (τ ∷ Γ₁) ≼ (τ ∷ Γ₂)
  drop : ∀ {Γ₁ Γ₂} → (τ : Type) →
         Γ₁ ≼ Γ₂ →
         Γ₁ ≼ (τ ∷ Γ₂)

weaken-var : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
weaken-var (keep τ Γ₁≼Γ₂) this = this
weaken-var (keep σ Γ₁≼Γ₂) (that x) = that (weaken-var Γ₁≼Γ₂ x)
weaken-var (drop τ₁ Γ₁≼Γ₂) x = that (weaken-var Γ₁≼Γ₂ x)
