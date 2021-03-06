module TermHSubst where

infixr 6 _⇒_

data Ty : Set where
  ○ : Ty
  _⇒_ : (σ : Ty) → (τ : Ty) → Ty

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : ∀ {Γ σ} → Var (Γ , σ) σ
  vs : ∀ {Γ σ τ} → Var Γ σ → Var (Γ , τ) σ

data Tm : Con → Ty → Set where
  var : ∀ {Γ τ} → Var Γ τ → Tm Γ τ
  app : ∀ {Γ σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  Λ : ∀ {Γ σ τ} → Tm (Γ , σ) τ → Tm Γ (σ ⇒ τ)

_-_ : {σ : Ty} → (Γ : Con) → Var Γ σ → Con
ε - ()
(Γ , σ) - vz = Γ
(Γ , τ) - vs x = (Γ - x) , τ

wkv : ∀ {Γ σ τ} → (x : Var Γ σ) → Var (Γ - x) τ → Var Γ τ
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

data EqV : ∀ {Γ σ τ} → Var Γ σ → Var Γ τ → Set where
  same : ∀ {Γ σ} → {x : Var Γ σ} → EqV x x
  diff : ∀ {Γ σ τ} → (x : Var Γ σ) → (z : Var (Γ - x) τ) → EqV x (wkv x z)
  -- If x and y do not represent the same variable, then
  -- ∃ z. y ≡ wkv x z, allowing us to construct a proof that diff x z : EqV x y

eq : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var Γ τ) → EqV x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
eq (vs y) (vs .y) | same = same
eq (vs x) (vs .(wkv x z)) | diff .x z = diff (vs x) (vs z)

wkTm : ∀ {Γ σ τ} → (x : Var Γ σ) → Tm (Γ - x) τ → Tm Γ τ
wkTm x (var v) = var (wkv x v)
wkTm x (app t₁ t₂) = (app (wkTm x t₁) (wkTm x t₂))
wkTm x (Λ t) = Λ (wkTm (vs x) t)

substVar : ∀ {Γ σ τ} → Var Γ τ → (x : Var Γ σ) → Tm (Γ - x) σ → Tm (Γ - x) τ
substVar v x u with eq x v
substVar v .v u | same = u
substVar .(wkv x z) x u | diff .x z = var z
-- The above is the crucial rule. The dotted pattern makes producing the result
-- easy.

subst : ∀ {Γ σ τ} → Tm Γ τ → (x : Var Γ σ) → Tm (Γ - x) σ → Tm (Γ - x) τ
subst (var v) x u = substVar v x u
subst (app t₁ t₂) x u = app (subst t₁ x u) (subst t₂ x u)
subst (Λ t) x u = Λ (subst t (vs x) (wkTm vz u))

import Relation.Binary.PropositionalEquality as P
open P hiding (subst)

eqRefl2 : ∀ {Γ σ τ} → (x : Var Γ σ) → eq x x ≡ same → eq (vs {τ = τ} x) (vs x) ≡ same
eqRefl2 x p with eq x x
eqRefl2 x refl | .same = refl

eqRefl : ∀ {Γ σ} → (x : Var Γ σ) → eq x x ≡ same
eqRefl vz = refl
eqRefl (vs x) = eqRefl2 x (eqRefl x)

substVarSame′ : ∀ {Γ σ} → (x : Var Γ σ) → (u : Tm (Γ - x) σ) → eq x x ≡ same → substVar x x u ≡ u
substVarSame′ x u p with eq x x
substVarSame′ x u refl | .same = refl

substVarSame : ∀ {Γ σ} → (x : Var Γ σ) → (u : Tm (Γ - x) σ) → substVar x x u ≡ u
substVarSame x u = substVarSame′ x u (eqRefl x)
