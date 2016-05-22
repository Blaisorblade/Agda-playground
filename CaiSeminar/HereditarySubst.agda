module HereditarySubst where

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

--
-- Now, let's combine subcontext relationship with the above machinery for
-- substitution.
--
-- First, standard subcontext relationship and weakening.

infix 4 _≼_
data _≼_ : (Γ₁ Γ₂ : Con) → Set where
  ∅ : ε ≼ ε
  keep : ∀ {Γ₁ Γ₂} → (τ : Ty) →
         Γ₁ ≼ Γ₂ →
         (Γ₁ , τ) ≼ (Γ₂ , τ)
  drop : ∀ {Γ₁ Γ₂} → (τ : Ty) →
         Γ₁ ≼ Γ₂ →
         Γ₁ ≼ (Γ₂ , τ)

wkv≼ : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
wkv≼ ∅ ()
wkv≼ (drop τ₁ Γ₁≼Γ₂) x = vs (wkv≼ Γ₁≼Γ₂ x)
wkv≼ (keep τ Γ₁≼Γ₂) vz = vz
wkv≼ (keep σ Γ₁≼Γ₂) (vs x) = vs (wkv≼ Γ₁≼Γ₂ x)
-- Caveat: we want the equation for wkv≼ (drop ...) to hold definitionally.
-- Reordering the equation can lose the ∅ case but makes that equation stop
-- holding definitionally; I guess we could prove it as a lemma by splitting on
-- the variable, but that's more cumbersome.

wkTm≼ : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Tm Γ₁ τ → Tm Γ₂ τ
wkTm≼ Γ₁≼Γ₂ (var x) = var (wkv≼ Γ₁≼Γ₂ x)
wkTm≼ Γ₁≼Γ₂ (app s t) = app (wkTm≼ Γ₁≼Γ₂ s) (wkTm≼ Γ₁≼Γ₂ t)
wkTm≼ Γ₁≼Γ₂ (Λ t) = Λ (wkTm≼ (keep _ Γ₁≼Γ₂) t)

--
-- Second, a (novel?) hybrid of both machineries.
--
-- Caveat: it might be easier to use Shub from McBride's "Dependently-typed
-- metaprogramming in Agda", but I haven't tried.
--

{-
-- True but unused
wkv′ : ∀ {Γ₁ Γ₂ σ τ} → (x : Var Γ₁ σ) → Γ₁ ≼ Γ₂ → Var (Γ₁ - x) τ → Var Γ₂ τ
wkv′ x Γ₁≼Γ₂ v = wkv≼ Γ₁≼Γ₂ (wkv x v)
-}

eq′ : ∀ {Γ₁ Γ₂ σ τ} → (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) → (x : Var Γ₁ σ) → (y : Var Γ₂ τ) → EqV (wkv≼ Γ₁≼Γ₂ x) y
eq′ Γ₁≼Γ₂ x y = eq (wkv≼ Γ₁≼Γ₂ x) y

_conDiff_ : ∀ {Γ₁ Γ₂ τ} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) (x : Var Γ₁ τ) → (Γ₁ - x) ≼ (Γ₂ - wkv≼ Γ₁≼Γ₂ x)
∅ conDiff ()
keep τ Γ₁≼Γ₂ conDiff vz = Γ₁≼Γ₂
keep τ Γ₁≼Γ₂ conDiff vs x = keep τ (Γ₁≼Γ₂ conDiff x)
drop τ Γ₁≼Γ₂ conDiff vz = drop τ (Γ₁≼Γ₂ conDiff vz)
drop τ Γ₁≼Γ₂ conDiff vs x = drop τ (Γ₁≼Γ₂ conDiff (vs x))

substVar≼ : ∀ {Γ₁ Γ₂ σ τ} → Var Γ₂ τ → (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) → (x : Var Γ₁ σ) → Tm (Γ₁ - x) σ → Tm (Γ₂ - wkv≼ Γ₁≼Γ₂ x) τ
substVar≼ v Γ₁≼Γ₂ x u with eq′ Γ₁≼Γ₂ x v
substVar≼ .(wkv≼ Γ₁≼Γ₂ x) Γ₁≼Γ₂ x u | same = wkTm≼ (Γ₁≼Γ₂ conDiff x) u
substVar≼ .(wkv (wkv≼ Γ₁≼Γ₂ x) z) Γ₁≼Γ₂ x u | diff .(wkv≼ Γ₁≼Γ₂ x) z = var z

subst≼ : ∀ {Γ₁ Γ₂ σ τ} → Tm Γ₂ τ → (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) → (x : Var Γ₁ σ) → Tm (Γ₁ - x) σ → Tm (Γ₂ - wkv≼ Γ₁≼Γ₂ x) τ
subst≼ (var v) Γ₁≼Γ₂ x u = substVar≼ v Γ₁≼Γ₂ x u
subst≼ (app t₁ t₂) Γ₁≼Γ₂ x u = app (subst≼ t₁ Γ₁≼Γ₂ x u) (subst≼ t₂ Γ₁≼Γ₂ x u)
subst≼ (Λ t) Γ₁≼Γ₂ x u = Λ (subst≼ t (drop _ Γ₁≼Γ₂) x u)
