module TypedDeBrujin where

open import Level

record Meaning (Syntax : Set) {ℓ : Level} : Set (suc ℓ) where
  constructor
    meaning
  field
    {Semantics} : Set ℓ
    ⟨_⟩⟦_⟧ : Syntax → Semantics

open Meaning {{...}} public
  renaming (⟨_⟩⟦_⟧ to ⟦_⟧)

data Type : Set where
  Int : Type
  _⇒_ : (σ : Type) → (τ : Type) → Type

open import Data.Integer

⟦_⟧Type : Type → Set
⟦ Int ⟧Type = ℤ
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type

instance
  meaningOfType = meaning ⟦_⟧Type

open import Data.List

Context : Set
Context = List Type

open import Data.List.All public
  renaming
    ( All to DependentList )

⟦_⟧Context = DependentList ⟦_⟧Type

instance
  meaningOfContext = meaning ⟦_⟧Context

data Var : Context → Type → Set where
  this : ∀ {τ Γ} → Var (τ ∷ Γ) τ
  that : ∀ {σ τ Γ} → Var Γ τ → Var (σ ∷ Γ) τ

⟦_⟧Var : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ this ⟧Var   (px ∷ ρ) = px
⟦ that v ⟧Var (px ∷ ρ) = ⟦ v ⟧Var ρ

instance
  meaningOfVar : ∀ {Γ τ} → Meaning (Var Γ τ)
  meaningOfVar = meaning ⟦_⟧Var

data Term : Context → Type → Set where
  lit : ∀ {Γ} → ℤ → Term Γ Int
  var : ∀ {Γ τ} → Var Γ τ → Term Γ τ
  app : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦_⟧Term (lit x) ρ = x
⟦_⟧Term (var x) ρ = ⟦ x ⟧Var ρ
⟦_⟧Term (app s t) ρ = ⟦ s ⟧Term ρ (⟦ t ⟧Term ρ)
⟦_⟧Term (lam t) ρ = λ x → ⟦ t ⟧Term (x ∷ ρ)
