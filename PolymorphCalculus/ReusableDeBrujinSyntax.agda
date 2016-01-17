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

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H

-- Inspired from answers to http://stackoverflow.com/q/24139810/53974. The
-- standard H.cong is not flexible enough. This probably belongs in the standard
-- library.
hcong : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ {x} → B x → Set c}
      {ax ay} {x : B ax} {y : B ay} (f : ∀ {z} (x : B z) → C x) →
      ax ≡ ay →
      x ≅ y → f x ≅ f y
hcong f refl refl = refl

-- Only works if τ is an index of Var, not a parameter O_O.
lemma-that-injective-≅ : ∀ {Γ σ₀ σ τ} {x₁ : Var Γ σ} {x₂ : Var Γ τ} → that {σ₀} x₁ ≅ that {σ₀} x₂ → x₁ ≅ x₂
lemma-that-injective-≅ refl = refl

-- Prove that the *type constructor* Var Γ is injective: if x₁ ≅ x₂, they're in
-- the same type, so Var Γ σ ≡ Var Γ τ. Hence, σ ≡ τ.
lemma-var-≅→types : ∀ {Γ σ τ} → (x₁ : Var Γ σ) → (x₂ : Var Γ τ) → x₁ ≅ x₂ → σ ≡ τ
lemma-var-≅→types this this x₁≅x₂ = refl
lemma-var-≅→types (that x₁) (that .x₁) refl = refl
lemma-var-≅→types this (that x₂) ()
lemma-var-≅→types (that x₁) this ()

var-≅ : ∀ {Γ σ τ} → (x₁ : Var Γ σ) → (x₂ : Var Γ τ) → Dec (x₁ ≅ x₂)
var-≅ this this = yes refl
var-≅ this (that x₂) = no (λ ())
var-≅ (that x₁) this = no (λ ())
var-≅ (that x₁) (that x₂) with var-≅ x₁ x₂
var-≅ (that x₁) (that x₂) | yes x₁≅x₂ = yes (hcong that (lemma-var-≅→types x₁ x₂ x₁≅x₂) x₁≅x₂)
var-≅ (that x₁) (that x₂) | no ¬x₁≅x₂ = no (λ that-x₁≅that-x₂ → ¬x₁≅x₂ (lemma-that-injective-≅ that-x₁≅that-x₂))

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

≼-refl : ∀ {Γ} → Γ ≼ Γ
≼-refl {[]} = ∅
≼-refl {x ∷ Γ} = keep x ≼-refl
