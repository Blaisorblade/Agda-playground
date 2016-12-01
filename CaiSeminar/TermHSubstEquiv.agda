module TermHSubstEquiv where

open import TermHSubst


data _βη-≡_ : ∀ {Γ σ} → Tm Γ σ → Tm Γ σ → Set where
  brefl : ∀ {Γ σ} {t : Tm Γ σ} →
    t βη-≡ t
  bsym : ∀ {Γ σ} {t₁ t₂ : Tm Γ σ} →
    t₁ βη-≡ t₂ → t₂ βη-≡ t₁
  btrans : ∀ {Γ σ} {t₁ t₂ t₃ : Tm Γ σ} →
    t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
  congΛ : ∀ {Γ σ τ} {t₁ t₂ : Tm (Γ , σ) τ} →
    t₁ βη-≡ t₂ → (Λ t₁) βη-≡ (Λ t₂)
  congApp : ∀ {Γ σ τ} {t₁ t₂ : Tm Γ (σ ⇒ τ)} {u₁ u₂} →
    t₁ βη-≡ t₂ → u₁ βη-≡ u₂ → (app t₁ u₁) βη-≡ (app t₂ u₂)
  beta : ∀ {Γ σ τ} {t : Tm (Γ , σ) τ} {u} →
    app (Λ t) u βη-≡ subst t vz u
  eta : ∀ {Γ σ τ} {t : Tm Γ (σ ⇒ τ)} →
    Λ (app (wkTm vz t) (var vz)) βη-≡ t
