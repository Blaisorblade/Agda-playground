module stlcTillmann where

postulate
  Prop : Set

data Formula : Set where
  prop : Prop → Formula
  _⊃_ : (A B : Formula) → Formula

infix 21 _,_
infix 22 _⊃_

data Formulae : Set where
  ∅ : Formulae
  _,_ : Formula → Formulae → Formulae

data _∈_ (A : Formula) : Formulae → Set where
  this : ∀ {Γ} →
    A ∈ A , Γ
  that : ∀ {B Γ} →
    A ∈ Γ →
    A ∈ B , Γ

data _⊢_ (Γ : Formulae) : Formula → Set where
  assumption : ∀ {A} → A ∈ Γ → Γ ⊢ A
  ⊃E : ∀ {A B} →
    Γ ⊢ A ⊃ B →
    Γ ⊢ A →
    Γ ⊢ B
  ⊃I : ∀ {A B} →
    A , Γ ⊢ B →
    Γ ⊢ A ⊃ B

data _⊢⋆_ (Γ : Formulae) : Formulae → Set where
  ∅ : Γ ⊢⋆ ∅
  _,_ : ∀ {A Δ} →
    Γ ⊢ A →
    Γ ⊢⋆ Δ →
    Γ ⊢⋆ A , Δ

cut : ∀ {A B Γ} →
  Γ ⊢ A →
  A , Γ ⊢ B →
  Γ ⊢ B
cut Γ⊢A AΓ⊢B = ⊃E (⊃I AΓ⊢B) Γ⊢A
{-# DISPLAY ⊃E (⊃I AΓ⊢B) Γ⊢A = cut Γ⊢A AΓ⊢B #-}

record Tarski : Set₁ where
  field _⊨p_ : Prop → Set

open Tarski

_⊨_ : Tarski → Formula → Set
_⊨⋆_ : Tarski → Formulae → Set

M ⊨ (prop p) = M ⊨p p
M ⊨ (A ⊃ B) = M ⊨ A → M ⊨ B

record ⊤ : Set where
  constructor tt

record _×_ (A B : Set) : Set where
  inductive
  constructor _,_
  field a : A
  field b : B

M ⊨⋆ ∅ = ⊤
M ⊨⋆ (x , Γ) = (M ⊨ x) × (M ⊨⋆ Γ)
