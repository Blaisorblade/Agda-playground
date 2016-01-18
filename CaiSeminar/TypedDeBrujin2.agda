module TypedDeBrujin2 where

data Type : Set where
  Nat : Type
  _⇒_ : Type → Type → Type

open import Data.Nat

⟦_⟧Type : Type → Set
⟦ Nat ⟧Type = ℕ
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type

open import Data.List hiding (drop)

Context : Set
Context = List Type

open import Data.List.All renaming (All to HList)

⟦_⟧Context = HList ⟦_⟧Type

data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ ∷ Γ) τ
  that : ∀ {Γ σ τ} → Var Γ τ → Var (σ ∷ Γ) τ

⟦_⟧Var : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦_⟧Var this (v ∷ ρ) = v
⟦_⟧Var (that v) (_ ∷ ρ) = ⟦ v ⟧Var ρ

data Term : Context → Type → Set where
  lit : ∀ {Γ} (v : ℕ) → Term Γ Nat
  var : ∀ {Γ τ} → Var Γ τ → Term Γ τ
  app : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  abs : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ lit v ⟧Term ρ = v
⟦ var x ⟧Term ρ = ⟦ x ⟧Var ρ
⟦ app s t ⟧Term ρ = ⟦ s ⟧Term ρ (⟦ t ⟧Term ρ)
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v ∷ ρ)

{-
weakenVar₁ : ∀ {Γ σ τ} → Var Γ τ → Var (σ ∷ Γ) τ
weakenVar₁ = that

weakenTerm₁ : ∀ {Γ σ τ} → Term Γ τ → Term (σ ∷ Γ) τ
weakenTerm₁ (lit v) = lit v
weakenTerm₁ (var x) = var (weakenVar₁ x)
weakenTerm₁ (app s t) = app (weakenTerm₁ s) (weakenTerm₁ t)
weakenTerm₁ (abs t) = abs {!!}

-}

infix 4 _≼_

data _≼_ : Context → Context → Set where
  ∅ : [] ≼ []
  keep : ∀ {Γ₁ Γ₂ τ} →
    Γ₁ ≼ Γ₂ →
    τ ∷ Γ₁ ≼ τ ∷ Γ₂
  drop : ∀ {Γ₁ Γ₂ τ} →
    Γ₁ ≼ Γ₂ →
    Γ₁ ≼ τ ∷ Γ₂


weakenVar : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
weakenVar (keep Γ₁≼Γ₂) this = this
weakenVar (keep Γ₁≼Γ₂) (that x) = that (weakenVar Γ₁≼Γ₂ x)
weakenVar (drop Γ₁≼Γ₂) x = that (weakenVar Γ₁≼Γ₂ x)

weakenTerm : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Term Γ₁ τ → Term Γ₂ τ
weakenTerm Γ₁≼Γ₂ (lit v) = lit v
weakenTerm Γ₁≼Γ₂ (var x) = var (weakenVar Γ₁≼Γ₂ x)
weakenTerm Γ₁≼Γ₂ (app s t) = app (weakenTerm Γ₁≼Γ₂ s) (weakenTerm Γ₁≼Γ₂ t)
weakenTerm Γ₁≼Γ₂ (abs t) = abs (weakenTerm (keep Γ₁≼Γ₂) t)

open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H
open import Relation.Nullary

var-≅? : ∀ {Γ σ τ} → (x₁ : Var Γ τ) → (x₂ : Var Γ σ) → Dec (x₁ ≅ x₂)
var-≅? = {!!}

lemma : ∀ {Γ σ τ} → (x₁ : Var Γ τ) → (x₂ : Var Γ σ) → x₁ ≅ x₂ → Var Γ σ ≡ Var Γ τ
lemma x₁ x₂ eq = {!eq!}

lemma′ : ∀ {A B : Set} → (x₁ : A) → (x₂ : B) → x₁ ≅ x₂ → A ≡ B
lemma′ x₁ .x₁ refl = refl

lemma2 : ∀ {Γ σ τ} → (x₁ : Var Γ σ) → (x₂ : Var Γ τ) → x₁ ≅ x₂ → Var Γ σ ≡ Var Γ τ
lemma2 = lemma′

term-subst : ∀ {Γ₁ Γ₂ σ τ} → Γ₁ ≼ Γ₂ → Var Γ₂ σ → Term Γ₁ σ → Term Γ₂ τ → Term Γ₂ τ
term-subst Γ₁≼Γ₂ x to-subst (lit v) = lit v
term-subst Γ₁≼Γ₂ x to-subst (var x₁) with var-≅? x x₁
term-subst Γ₁≼Γ₂ x to-subst (var x₁) | yes p = {!!}
term-subst Γ₁≼Γ₂ x to-subst (var x₁) | no ¬p = var x₁
term-subst Γ₁≼Γ₂ x to-subst (app s t) = app (term-subst Γ₁≼Γ₂ x to-subst s) (term-subst Γ₁≼Γ₂ x to-subst t)
term-subst Γ₁≼Γ₂ x to-subst (abs t) = abs (term-subst (drop Γ₁≼Γ₂) (that x) to-subst t)
