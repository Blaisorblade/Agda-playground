module TypedDeBrujin where

data Type : Set where
  Int : Type
  _⇒_ : (σ : Type) → (τ : Type) → Type

open import Data.Integer

⟦_⟧Type : Type → Set
⟦ Int ⟧Type = ℤ
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type

open import Data.List
  -- using (List; []; _∷_)
  hiding (drop)

Context : Set
Context = List Type

open import Data.List.All public
  renaming
    ( All to HList )

⟦_⟧Context = HList ⟦_⟧Type

data Var : Context → Type → Set where
  this : ∀ {τ Γ} → Var (τ ∷ Γ) τ
  that : ∀ {σ τ Γ} → Var Γ τ → Var (σ ∷ Γ) τ

⟦_⟧Var : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ this ⟧Var   (px ∷ ρ) = px
⟦ that v ⟧Var (px ∷ ρ) = ⟦ v ⟧Var ρ

data Term : Context → Type → Set where
  lit : ∀ {Γ} → ℤ → Term Γ Int
  var : ∀ {Γ τ} → Var Γ τ → Term Γ τ
  app : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦_⟧Term (lit x) ρ = x
⟦_⟧Term (var x) ρ = ⟦ x ⟧Var ρ
⟦_⟧Term (app s t) ρ = ⟦ s ⟧Term ρ (⟦ t ⟧Term ρ)
⟦_⟧Term (lam t) ρ = λ x → ⟦ t ⟧Term (x ∷ ρ)

weakenVar₁ : ∀ {Γ σ τ} → Var Γ τ → Var (σ ∷ Γ) τ
weakenVar₁ = that

-- Failed attempt
{-
weakenTerm₁ : ∀ {Γ σ τ} → Term Γ τ → Term (σ ∷ Γ) τ
weakenTerm₁ (lit x) = lit x
weakenTerm₁ (var x) = var (weakenVar₁ x)
weakenTerm₁ (app s t) = app (weakenTerm₁ s) (weakenTerm₁ t)
weakenTerm₁ (lam t) = lam {!!}
-}

infix 4 _≼_

data _≼_ : (Γ₁ Γ₂ : Context) → Set where
  ∅ : [] ≼ []
  keep : ∀ {Γ₁ Γ₂} →
    (τ : Type) →
    Γ₁ ≼ Γ₂ →
    τ ∷ Γ₁ ≼ τ ∷ Γ₂
  drop : ∀ {Γ₁ Γ₂} →
    (τ : Type) →
    Γ₁ ≼ Γ₂ →
    Γ₁ ≼ τ ∷ Γ₂

≼-refl : ∀ {Γ} → Γ ≼ Γ
≼-refl {[]} = ∅
≼-refl {τ ∷ Γ} = keep τ ≼-refl

≼-trans : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ≼ Γ₂ → Γ₂ ≼ Γ₃ → Γ₁ ≼ Γ₃
≼-trans ≼₁ ∅ = ≼₁
≼-trans (keep τ ≼₁) (keep .τ ≼₂) = keep τ (≼-trans ≼₁ ≼₂)
≼-trans (drop τ ≼₁) (keep .τ ≼₂) = drop τ (≼-trans ≼₁ ≼₂)
≼-trans ≼₁ (drop τ ≼₂) = drop τ (≼-trans ≼₁ ≼₂)

weaken-var-int : ∀ Γ₁ Γ₂ τ → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
weaken-var-int (.τ ∷ Γ₁) (.τ ∷ Γ₂) .τ (keep τ Γ≼) this = this
weaken-var-int ._ (σ ∷ Γ₂) τ (keep .σ Γ≼) (that x) = that (weaken-var-int _ _ _ Γ≼ x)
weaken-var-int Γ₁ (τ₁ ∷ Γ₂) τ (drop .τ₁ Γ≼) x = that (weaken-var-int _ _ _ Γ≼ x)

weaken-var : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
weaken-var (keep _ Γ≼) this = this
weaken-var (keep _ Γ≼) (that x) = that (weaken-var Γ≼ x)
weaken-var (drop _ Γ≼) x = that (weaken-var Γ≼ x)

weaken-term : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Term Γ₁ τ → Term Γ₂ τ
weaken-term Γ≼ (lit v) = lit v
weaken-term Γ≼ (var x) = var (weaken-var Γ≼ x)
weaken-term Γ≼ (app s t) = app (weaken-term Γ≼ s) (weaken-term Γ≼ t)
weaken-term Γ≼ (lam t) = lam (weaken-term (keep _ Γ≼) t)

-- Bundling variable comparison in the same function doesn't work well.
{-
subst : ∀ {Γ₁ Γ₂ σ τ} → Γ₁ ≼ Γ₂ → Term Γ₁ σ → Var Γ₂ σ → Term Γ₂ τ → Term Γ₂ τ
subst Γ≼ s x (lit v) = lit v
subst Γ≼ s x (app t₁ t₂) = app (subst Γ≼ s x t₁) (subst Γ≼ s x t₂)
subst Γ≼ s x (lam t) = lam (subst (drop _ Γ≼) s (that x) t)
-- subst Γ≼ s x (var x₁) with equality... = {!var!}
subst Γ≼ s this (var this) = weaken-term Γ≼ s
subst Γ≼ s (that x) (var (that x₁)) = subst ≼-refl (weaken-term Γ≼ s) (that x) (var (that x₁))
subst Γ≼ s this (var (that x₁)) = var (that x₁)
subst Γ≼ s (that x) (var this) = var this
-}

open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H
open import Relation.Nullary


injective-that : ∀ {Γ σ₀ σ τ} {x₁ : Var Γ σ} {x₂ : Var Γ τ} → that {σ₀} x₁ ≅ that {σ₀} x₂ → x₁ ≅ x₂
injective-that refl = refl

{-
-- These guys are hard to write.
induces-types : ∀ {c a b} {Z : Set c} {A : Z → Set a} {B : ∀ {z} → A z → Set b}
  {zx zy} {x : A zx} {y : A zy}
  (f : ∀ {z} → (x : A z) → B x) → x ≅ y → A zx ≅ A zy
induces-types {x = x} {y = y} f x≅y = {!H.subst !}

cong-better : ∀ {c a b} {Z : Set c} {A : Z → Set a} {B : ∀ {z} → A z → Set b}
  {zx zy} {x : A zx} {y : A zy}
  (f : ∀ {z} → (x : A z) → B x) → x ≅ y → f x ≅ f y
cong-better f eq = {!eq!}

-- So we can't use this.
var-≡? : ∀ {Γ σ τ} → (x₁ : Var Γ σ) → (x₂ : Var Γ τ) → Dec (x₁ ≅ x₂)
var-≡? this this = yes refl
var-≡? this (that x₂) = no (λ ())
var-≡? (that x₁) this = no (λ ())
var-≡? (that x₁) (that x₂) with var-≡? x₁ x₂
var-≡? (that x₁) (that x₂) | yes p = yes (cong-better {A = Var _} (λ x → that x) p)
var-≡? (that x₁) (that x₂) | no ¬p = no (λ x → ¬p (injective-that x))
-}

open import Data.Maybe
open import Data.Product

-- From answers to http://stackoverflow.com/q/24139810/53974.
cong-better : ∀ {c a b} {Z : Set c} {A : Z → Set a} {B : ∀ {z} → A z → Set b}
  {zx zy} {x : A zx} {y : A zy} →
  zx ≡ zy →
  (f : ∀ {z} → (x : A z) → B x) → x ≅ y → f x ≅ f y
cong-better refl f refl = refl

var-≅? : ∀ {Γ σ τ} → (x₁ : Var Γ σ) → (x₂ : Var Γ τ) → Dec (σ ≡ τ × x₁ ≅ x₂)
var-≅? this this = yes (refl , refl)
var-≅? this (that x₂) = no (λ {(σ≡τ , ())})
var-≅? (that x₁) this = no (λ {(σ≡τ , ())})
var-≅? (that x₁) (that x₂) with var-≅? x₁ x₂
var-≅? (that x₁) (that x₂) | yes (σ≡τ , x₁≅x₂) = yes (σ≡τ , cong-better {A = Var _} σ≡τ (λ x → that x) x₁≅x₂)
var-≅? (that x₁) (that x₂) | no ¬p = no (λ {(σ≡τ , that-x₁≅that-x₂) → ¬p (σ≡τ , injective-that that-x₁≅that-x₂)})

var-types-≡? : ∀ {Γ σ τ} → (x₁ : Var Γ σ) → (x₂ : Var Γ τ) → Maybe (σ ≡ τ)
var-types-≡? x₁ x₂ with var-≅? x₁ x₂
... | yes (σ≡τ , x₁≅x₂) = just σ≡τ
... | no ¬p = nothing

term-subst-int : ∀ {Γ σ τ} → Term Γ σ → Var Γ σ → Term Γ τ → Term Γ τ
term-subst-int s x (lit v) = lit v
term-subst-int s x (app t₁ t₂) = app (term-subst-int s x t₁) (term-subst-int s x t₂)
term-subst-int s x (lam t) = lam (term-subst-int (weaken-term (drop _ ≼-refl) s) (that x) t)
term-subst-int s x (var x₁) with var-types-≡? x x₁
-- Failed attempt, but at nonsense
--term-subst-int s x (var x₁) | yes p = var (H.subst (λ x → x) (induces-types {A = Var _} (λ x → x) p) x)
-- Successful nonsense
--term-subst-int s x (var x₁) | yes (σ≡τ , x≅x₁) = var (P.subst (λ x → x) (P.cong (Var _) σ≡τ) x)
-- Simpler nonsense
--term-subst-int s x (var x₁) | yes (refl , x≅x₁) = var x
-- Correct solution
term-subst-int s x (var x₁) | just refl = s
term-subst-int s x (var x₁) | nothing = var x₁
term-subst : ∀ {Γ₁ Γ₂ σ τ} → Γ₁ ≼ Γ₂ → Term Γ₁ σ → Var Γ₂ σ → Term Γ₂ τ → Term Γ₂ τ
term-subst Γ≼ s x t = term-subst-int (weaken-term Γ≼ s) x t
