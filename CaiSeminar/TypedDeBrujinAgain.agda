module TypedDeBrujinAgain where

data Type : Set where
  Nat : Type
  _⇒_ : (σ : Type) → (τ : Type) → Type

open import Data.Nat

⟦_⟧Type : Type → Set
⟦ Nat ⟧Type = ℕ
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type

open import Data.List hiding (drop)

Context : Set
Context = List Type

open import Data.List.All renaming (All to HList)

-- The semantics of a typing context is an environment
⟦_⟧Context : Context → Set
⟦_⟧Context = HList ⟦_⟧Type

data Var : Type → Context → Set where
  this : ∀ {Γ τ} → Var τ (τ ∷ Γ)
  that : ∀ {σ Γ τ} → Var τ Γ → Var τ (σ ∷ Γ)

⟦_⟧Var : ∀ {Γ τ} → Var τ Γ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ this ⟧Var   (v ∷ ρ) = v
⟦ that x ⟧Var (v ∷ ρ) = ⟦ x ⟧Var ρ

data Term : Type → Context → Set where
  lit : ∀ {Γ} → (v : ℕ) → Term Nat Γ
  var : ∀ {τ Γ} → Var τ Γ → Term τ Γ
  app : ∀ {σ τ Γ} → Term (σ ⇒ τ) Γ → Term σ Γ → Term τ Γ
  lam : ∀ {σ τ Γ} → Term τ (σ ∷ Γ) → Term (σ ⇒ τ) Γ

⟦_⟧Term : ∀ {τ Γ} → Term τ Γ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦_⟧Term (lit v) ρ = v
⟦_⟧Term (var x) ρ = ⟦ x ⟧Var ρ
⟦_⟧Term (app s t) ρ = ⟦ s ⟧Term ρ (⟦ t ⟧Term ρ)
⟦_⟧Term (lam t) ρ = λ v → ⟦ t ⟧Term (v ∷ ρ)

weakenVar₁ : ∀ {Γ σ τ} → Var τ Γ → Var τ (σ ∷ Γ)
weakenVar₁ = that

{-
weakenTerm₁ : ∀ {Γ σ τ} → Term τ Γ → Term τ (σ ∷ Γ)

-- We can't implement this.
weakenTerm₁ (lit x) = lit x
weakenTerm₁ (var x) = var (weakenVar₁ x)
weakenTerm₁ (app s t) = app (weakenTerm₁ s) (weakenTerm₁ t)
weakenTerm₁ (lam t) = lam {!!}
-}

infix 4 _≼_
data _≼_ : (Γ₁ Γ₂ : Context) → Set where
  ∅ : [] ≼ []
  keep : ∀ {Γ₁ Γ₂} → (τ : Type) →
         Γ₁ ≼ Γ₂ →
         (τ ∷ Γ₁) ≼ (τ ∷ Γ₂)
  drop : ∀ {Γ₁ Γ₂} → (τ : Type) →
         Γ₁ ≼ Γ₂ →
         Γ₁ ≼ (τ ∷ Γ₂)

weaken-var : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var τ Γ₁ → Var τ Γ₂
weaken-var (keep τ Γ₁≼Γ₂) this = this
weaken-var (keep σ Γ₁≼Γ₂) (that x) = that (weaken-var Γ₁≼Γ₂ x)
weaken-var (drop τ₁ Γ₁≼Γ₂) x = that (weaken-var Γ₁≼Γ₂ x)

weaken-term : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Term τ Γ₁ → Term τ Γ₂
weaken-term Γ₁≼Γ₂ (lit v) = lit v
weaken-term Γ₁≼Γ₂ (var x) = var (weaken-var Γ₁≼Γ₂ x)
weaken-term Γ₁≼Γ₂ (app s t) = app (weaken-term Γ₁≼Γ₂ s) (weaken-term Γ₁≼Γ₂ t)
weaken-term Γ₁≼Γ₂ (lam t) = lam (weaken-term (keep _ Γ₁≼Γ₂) t)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H

-- From answers to http://stackoverflow.com/q/24139810/53974.
hcong : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ {x} → B x → Set c}
      {ax ay} {x : B ax} {y : B ay} (f : ∀ {z} (x : B z) → C x) →
      ax ≡ ay →
      x ≅ y → f x ≅ f y
hcong f refl refl = refl

-- Only works if τ is an index of Var, not a parameter O_O.
that-injective : ∀ {Γ σ₀ σ τ} {x₁ : Var σ Γ} {x₂ : Var τ Γ} → that {σ₀} x₁ ≅ that {σ₀} x₂ → x₁ ≅ x₂
that-injective refl = refl

var-≅→types : ∀ {Γ σ τ} → (x₁ : Var σ Γ) → (x₂ : Var τ Γ) → x₁ ≅ x₂ → σ ≡ τ
var-≅→types this this x₁≅x₂ = refl
var-≅→types (that x₁) (that .x₁) refl = refl
var-≅→types this (that x₂) ()
var-≅→types (that x₁) this ()

var-≅ : ∀ {Γ σ τ} → (x₁ : Var σ Γ) → (x₂ : Var τ Γ) → Dec (x₁ ≅ x₂)
var-≅ this this = yes refl
var-≅ this (that x₂) = no (λ ())
var-≅ (that x₁) this = no (λ ())
var-≅ (that x₁) (that x₂) with var-≅ x₁ x₂
var-≅ (that x₁) (that x₂) | yes x₁≅x₂ = yes (hcong that (var-≅→types x₁ x₂ x₁≅x₂) x₁≅x₂)
var-≅ (that x₁) (that x₂) | no ¬p = no (λ that-x₁≅that-x₂ → ¬p (that-injective that-x₁≅that-x₂))

term-subst : ∀ {Γ₁ Γ₂ σ τ} → Γ₁ ≼ Γ₂ → Var σ Γ₂ → Term σ Γ₁ → Term τ Γ₂ → Term τ Γ₂
term-subst Γ₁≼Γ₂ x to-subst (lit v) = lit v
term-subst Γ₁≼Γ₂ x to-subst (app s t) = app (term-subst Γ₁≼Γ₂ x to-subst s) (term-subst Γ₁≼Γ₂ x to-subst t)
term-subst Γ₁≼Γ₂ x to-subst (lam t) = lam (term-subst (drop _ Γ₁≼Γ₂) (that x) to-subst t)
term-subst Γ₁≼Γ₂ x to-subst (var x₁) with var-≅ x x₁
term-subst Γ₁≼Γ₂ x to-subst (var x₁) | yes p = weaken-term Γ₁≼Γ₂ (P.subst (λ τ → Term τ _) (var-≅→types _ _ p) to-subst  )
term-subst Γ₁≼Γ₂ x to-subst (var x₁) | no ¬p = var x₁
