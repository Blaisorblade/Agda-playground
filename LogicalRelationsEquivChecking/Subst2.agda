module Subst2 where

open import Term

open import Data.List
_<><_ : Con → List Ty → Con
Γ <>< [] = Γ
Γ <>< (x ∷ xs) = (Γ , x) <>< xs

Ren Sub Shub : Con → Con → Set
Ren Γ Δ = ∀ {τ} → Var Γ τ → Var Δ τ
Sub Γ Δ = ∀ {τ} → Var Γ τ → Tm Δ τ
Shub Γ Δ = ∀ Ξ → Sub (Γ <>< Ξ) (Δ <>< Ξ)

wkθ : ∀ {Γ Δ} σ → Shub Γ Δ → Shub (Γ , σ) (Δ , σ)
wkθ σ θ = λ Ξ → θ (σ ∷ Ξ)

infixr 15 _//_
_//_ : ∀ {Γ Δ} (θ : Shub Γ Δ) {τ} → Tm Γ τ → Tm Δ τ
θ // var x = θ [] x
θ // app s t = app (θ // s) (θ // t)
θ // Λ {σ = σ} t = Λ (wkθ σ θ // t)
θ // c k = c k

wkr : ∀ {Γ Δ σ} → Ren Γ Δ → Ren (Γ , σ) (Δ , σ)
wkr r vz = vz
wkr r (vs v) = vs (r v)

ren : ∀ {Γ Δ} → Ren Γ Δ → Shub Γ Δ
ren r [] x = var (r x)
ren r (_ ∷ Ξ) = ren (wkr r) Ξ

renSub : ∀ {Γ Δ} → Ren Γ Δ → Sub Γ Δ
renSub θ = λ x → var (θ x)

wks : ∀ {Γ Δ σ} → Sub Γ Δ → Sub (Γ , σ) (Δ , σ)
wks s vz = var vz
wks s (vs x) = ren vs // s x

sub : ∀ {Γ Δ} → Sub Γ Δ → Shub Γ Δ
sub s [] = s
sub s (_ ∷ Ξ) = sub (wks s) Ξ

weak : ∀ {Γ} Ξ → Ren Γ (Γ <>< Ξ)
weak [] x = x
weak (_ ∷ Ξ) x = weak Ξ (vs x)

_-_ : ∀ Γ {τ} (x : Var Γ τ) → Con

(Γ , τ) - vz = Γ
(Γ , τ) - vs x = Γ - x , τ

_/=_ : ∀ Γ {τ} (x : Var Γ τ) → Ren (Γ - x) Γ
(Γ , τ) /= vz = vs
(Γ , τ) /= vs x = wkr (Γ /= x)

wkv : ∀ {Γ σ τ} → (x : Var Γ σ) → Var (Γ - x) τ → Var Γ τ
wkv x = _ /= x


data EqV : ∀ {Γ σ τ} → Var Γ σ → Var Γ τ → Set where
  same : ∀ {Γ σ} → {x : Var Γ σ} → EqV x x
  diff : ∀ {Γ σ τ} → (x : Var Γ σ) → (z : Var (Γ - x) τ) → EqV x {-(wkv x z)-}((Γ /= x) z)
  -- If x and y do not represent the same variable, then
  -- ∃ z. y ≡ wkv x z, allowing us to construct a proof that diff x z : EqV x y

eq : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var Γ τ) → EqV x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
eq (vs y) (vs .y) | same = same
eq (vs x) (vs .(wkv x z)) | diff .x z = diff (vs x) (vs z)

atomicSubst : ∀ {Γ σ} → (x : Var Γ σ) → Tm (Γ - x) σ → Sub Γ (Γ - x)
atomicSubst x u v with eq x v
atomicSubst v u .v | same = u
atomicSubst x u _ | diff .x z = var z

substSub : ∀ {Γ Δ τ} → Sub Γ Δ → Tm Γ τ → Tm Δ τ
substSub s t = sub s // t

wkTm : ∀ {Γ Δ τ} → Ren Γ Δ → Tm Γ τ → Tm Δ τ
wkTm r t = ren r // t

wkTm′ : ∀ {Γ σ τ} → (x : Var Γ σ) → Tm (Γ - x) τ → Tm Γ τ
wkTm′ x t = wkTm (wkv x) t

subst : ∀ {Γ σ τ} → (x : Var Γ σ) → Tm (Γ - x) σ → Tm Γ τ → Tm (Γ - x) τ
subst x u = substSub (atomicSubst x u)
