module Term (Const : Set) where

infixr 6 _⇒_

data Ty : Set where
  b : Ty
  _⇒_ : (σ : Ty) → (τ : Ty) → Ty

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con

infixl 4 _,_

data Var : Con → Ty → Set where
  vz : ∀ {Γ σ} → Var (Γ , σ) σ
  vs : ∀ {Γ σ τ} → Var Γ σ → Var (Γ , τ) σ

data Tm : Con → Ty → Set where
  var : ∀ {Γ τ} → Var Γ τ → Tm Γ τ
  app : ∀ {Γ σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  Λ : ∀ {Γ σ τ} → Tm (Γ , σ) τ → Tm Γ (σ ⇒ τ)
  c : ∀ {Γ} (k : Const) → Tm Γ b
