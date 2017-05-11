module EquivSubst1 where
open import Term
open import Subst1

data _βη-≡_ : ∀ {Γ Δ σ τ} → Tm Γ σ → Tm Δ τ → Set where
  Q-Refl : ∀ {Γ σ} {t : Tm Γ σ} →
    t βη-≡ t
  Q-Symm : ∀ {Γ σ} {t₁ t₂ : Tm Γ σ} →
    t₁ βη-≡ t₂ → t₂ βη-≡ t₁
  Q-Trans : ∀ {Γ σ} {t₁ t₂ t₃ : Tm Γ σ} →
    t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
  Q-Abs : ∀ {Γ σ τ} {t₁ t₂ : Tm (Γ , σ) τ} →
    t₁ βη-≡ t₂ →
    (Λ t₁) βη-≡ (Λ t₂)
  Q-App : ∀ {Γ σ τ} {t₁ t₂ : Tm Γ (σ ⇒ τ)} {u₁ u₂} →
    t₁ βη-≡ t₂ → u₁ βη-≡ u₂ → (app t₁ u₁) βη-≡ (app t₂ u₂)
  Q-Beta : ∀ {Γ σ τ} {t : Tm (Γ , σ) τ} {u} →
    app (Λ t) u βη-≡ subst t vz u

  Q-Eta : ∀ {Γ σ τ} {t : Tm Γ (σ ⇒ τ)} →
    Λ (app (wkTm vz t) (var vz)) βη-≡ t
{-
  Q-Ext :
    ∀ {Γ σ τ} {s t : Tm Γ (σ ⇒ τ)} →
    app (wkTm vz s) (var vz) βη-≡ app (wkTm vz t) (var vz) →
    s βη-≡ t
-}
{-
  Q-Ext :
    ∀ {Γ σ τ} {x} {s t : Tm (Γ -x x) (σ ⇒ τ)} →
    app (wkTm′ x s) (var x) βη-≡ app (wkTm′ x t) (var x) →
    s βη-≡ t
-}

{-
wkβη-≡ : ∀ {Γ σ τ} (x : Var Γ σ) {t₁ t₂ : Tm (Γ - x) τ} → t₁ βη-≡ t₂ → wkTm x t₁ βη-≡ wkTm x t₂
wkβη-≡ x Q-Refl = Q-Refl
wkβη-≡ x (Q-Symm Eq) = Q-Symm (wkβη-≡ x Eq)
wkβη-≡ x (Q-Trans Eq Eq₁) = Q-Trans (wkβη-≡ x Eq) (wkβη-≡ x Eq₁)
wkβη-≡ x (Q-Abs Eq) = Q-Abs (wkβη-≡ (vs x) Eq)
wkβη-≡ x (Q-App Eq Eq₁) = Q-App (wkβη-≡ x Eq) (wkβη-≡ x Eq₁)
wkβη-≡ x Q-Beta = {!Q-Beta!}
wkβη-≡ x (Q-Ext Eq) = Q-Ext {!wkβη-≡ x Eq!}

{-
Given Γ ⊢ t : σ ⇒ τ, prove
Γ ⊢ λ x. t x ?= t. That is,
Γ , y ⊢ (λ x . t x) y = t y. Use transitivity to get to
Γ , y ⊢ (λ x . t x) y = t x [ x := y ] = t y.

t′ = (wkTm vz .t)
Goal: subst (app (wkTm (vs vz) t′) (var vz)) vz (var vz)
      βη-≡ app t′ (var vz)

Goal: app (subst (wkTm (vs vz) t′) vz (var vz)) (var vz)
      βη-≡ app t′ (var vz)

-}
-- {!(wkTm (vs y) (wkTm x t)) x y!} vz (var vz)
Q-Contraction : ∀ {Γ τ σ₁} (x : Var Γ σ₁) (y : Var (Γ - x) σ₁) (t : Tm ((Γ - x) - y) τ) →
  subst (wkTm (wkv x y) {!wkTm y t!}) x (var y) βη-≡ wkTm y t
Q-Contraction t = {!subst t vz  !}
Q-Eta : ∀ {Γ σ τ} {t : Tm Γ (σ ⇒ τ)} →
    Λ (app (wkTm vz t) (var vz)) βη-≡ t
Q-Eta {t = t} = Q-Ext (Q-Trans Q-Beta (Q-App {!Q-Contraction vz vz t !} Q-Refl))
--(Q-App (wkβη-≡ vz {!Q-Beta!}) Q-Refl)
{-
(wk y (wk x t)) [x := y] = wk x t
-}
-}

Q-Ext : ∀ {Γ σ τ} (s t : Tm Γ (σ ⇒ τ)) →
  app (wkTm vz s) (var vz) βη-≡ app (wkTm vz t) (var vz) →
  s βη-≡ t
Q-Ext s t βη-≡ = Q-Trans (Q-Trans (Q-Symm Q-Eta) (Q-Abs βη-≡)) Q-Eta

import Relation.Binary.PropositionalEquality as P
import Relation.Binary.HeterogeneousEquality as H
open P hiding (subst)
open H hiding (subst)

{-

Γ-x-y-comm : ∀ {Γ τ σ₁} (x : Var Γ σ₁) (y : Var (Γ - x) σ₁) → ((Γ - x) - y) ≡ {!Γ - y!}
Γ-x-y-comm = {!!}

wkSubst : ∀ {Γ σ σ₁ τ} → (t : Tm (Γ , σ₁) τ) → (x : Var Γ σ) (y : Var (Γ , σ₁) σ) → (u : {! Tm ((Γ , σ₁) - x) σ !}) →  {!!} βη-≡ wkTm x {! subst t y u !}
wkSubst = {!!}

-}

wkCommV : ∀ {Γ σ₁ σ₂} → (x : Var Γ σ₁) (y : Var (Γ - x) σ₂) → x ≡ wkv (wkv x y) (swap x y)
wkCommV vz y = refl
wkCommV (vs x) vz = refl
wkCommV (vs x) (vs y) = P.cong vs (wkCommV x y)

mySubst : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≡ Γ₂ → Tm Γ₁ τ → Tm Γ₂ τ
mySubst refl t = t

open import Data.Product hiding (swap)

wkCommStmβ : ∀ {Γ τ σ σ₁} → (x : Var Γ σ) → (y : Var (Γ - x) σ₁) (t : Tm (Γ - x - y) τ) → Set
wkCommStmβ {Γ} {τ} {σ} {σ₁} x y t with swapCtx _ _ _ x y | swapCtxT x y t
wkCommStmβ x y t | p | t′ , t′≡t =
    wkTm (wkv x y) (wkTm (swap x y) t′)
  βη-≡
    wkTm x (wkTm y t)
wkCommβ : ∀ {Γ τ σ σ₁} → (x : Var Γ σ) → (y : Var (Γ - x) σ₁) (t : Tm (Γ - x - y) τ) →
  wkCommStmβ x y t
wkCommβ vz vz (var x) = Q-Refl
wkCommβ vz vz (app t t₁) = Q-App (wkCommβ vz vz t) (wkCommβ vz vz t₁)
wkCommβ vz vz (Λ t) = Q-Abs (wkCommβ (vs vz) (vs vz) t)
wkCommβ vz vz (c k) = Q-Refl
wkCommβ vz (vs y) t = {!!}
wkCommβ (vs x) vz t = {!!}
wkCommβ (vs x) (vs y) (var x₁) = {!!}
wkCommβ (vs x) (vs y) (app t t₁) = {!!}
wkCommβ (vs x) (vs y) (Λ t) = {!!}
wkCommβ (vs x) (vs y) (c k) = {!wkCommβ x y (c k)!}

wkCommStm : ∀ {Γ τ σ σ₁} → (x : Var Γ σ) → (y : Var (Γ - x) σ₁) (t : Tm (Γ - x - y) τ) → Set
wkCommStm {Γ} {τ} {σ} {σ₁} x y t with swapCtx _ _ _ x y | swapCtxT x y t
wkCommStm x y t | p | t′ , t′≡t =
    wkTm (wkv x y) (wkTm (swap x y) t′)
  ≅
    wkTm x (wkTm y t)

wkComm : ∀ {Γ τ σ σ₁} → (x : Var Γ σ) → (y : Var (Γ - x) σ₁) (t : Tm (Γ - x - y) τ) →
  wkCommStm x y t
wkComm vz vz (var x) = refl
wkComm vz vz (app s t) = H.cong₂ app (wkComm vz vz s) (wkComm vz vz t)
wkComm vz vz (Λ t) = H.cong Λ (wkComm (vs vz) (vs vz) t)
wkComm vz vz (c k) = refl
wkComm vz (vs y) (var x) = refl
wkComm vz (vs y) (app s t) = H.cong₂ app (wkComm vz (vs y) s) (wkComm vz (vs y) t)
wkComm vz (vs y) (Λ t) = H.cong Λ (wkComm (vs vz) (vs (vs y)) t)
wkComm vz (vs y) (c k) = refl
wkComm (vs x) vz (var x₁) = refl
wkComm (vs x) vz (app s t) = H.cong₂ app (wkComm (vs x) vz s) (wkComm (vs x) vz t)
wkComm (vs x) vz (Λ t) = H.cong Λ (wkComm (vs (vs x)) (vs vz) t)
wkComm (vs x) vz (c k) = refl
wkComm (vs x) (vs y) (var x₁) = {!x₁!}
wkComm (vs x) (vs y) (app t t₁) = {!!}
wkComm (vs x) (vs y) (Λ t) = {!!}
wkComm (vs x) (vs y) (c k) = {!!}

-- H.trans (H.cong (λ z → wkTm (wkv x y) (wkTm (swap x y) z)) {!subst-removable (λ □ → Tm □ _) (≡-to-≅ (swapCtx _ _ _ x y)) t!}) {!!}
wkCommR : ∀ {Γ τ σ σ₁} → (x : Var Γ σ) → (t : Tm (Γ - x) τ) →
   wkTm (vs {τ = σ₁} x) (wkTm vz t) βη-≡ wkTm vz (wkTm x t)
wkCommR x (var x₁) = Q-Refl
wkCommR x (app s t) = Q-App (wkCommR x s) (wkCommR x t)
wkCommR x (Λ t) = Q-Abs {!!}
wkCommR x (c k) = Q-Refl

≡-to-βη-≡ : ∀ {Γ τ} {t₁ t₂ : Tm Γ τ} → t₁ ≅ t₂ → t₁ βη-≡ t₂
≡-to-βη-≡ refl = Q-Refl

--subst : ∀ {Γ σ τ} → Tm Γ τ → (x : Var Γ σ) → Tm (Γ - x) σ → Tm (Γ - x) τ

-- True but too weak to prove recursively.
wkSubstR : ∀ {Γ σ σ₁ τ} → (x : Var Γ σ) → (t : Tm ((Γ - x), σ₁) τ) → (u : Tm (Γ - x) σ₁) →  subst (wkTm (vs x) t) vz (wkTm x u) βη-≡ wkTm x (subst t vz u)
wkSubstR x (var x₁) u = {!!}
wkSubstR x (app s t) u = Q-App (wkSubstR x s u) (wkSubstR x t u)
wkSubstR x (Λ t) u = Q-Abs {!wkSubstR (vs x) t!}
wkSubstR x (c k) u = Q-Refl

-- True but depends on unproven lemmas.
wkβη-≡ : ∀ {Γ σ τ} (x : Var Γ σ) {t₁ t₂ : Tm (Γ - x) τ} → t₁ βη-≡ t₂ → wkTm x t₁ βη-≡ wkTm x t₂
wkβη-≡ x Q-Refl = Q-Refl
wkβη-≡ x (Q-Symm Eq) = Q-Symm (wkβη-≡ x Eq)
wkβη-≡ x (Q-Trans Eq Eq₁) = Q-Trans (wkβη-≡ x Eq) (wkβη-≡ x Eq₁)
wkβη-≡ x (Q-Abs Eq) = Q-Abs (wkβη-≡ (vs x) Eq)
wkβη-≡ x (Q-App Eq Eq₁) = Q-App (wkβη-≡ x Eq) (wkβη-≡ x Eq₁)
wkβη-≡ x (Q-Beta {t = t} {u = u}) = Q-Trans Q-Beta (wkSubstR x t u)
wkβη-≡ x (Q-Eta {t = t}) = Q-Trans (Q-Abs (Q-App (≡-to-βη-≡ (wkComm vz x t)) Q-Refl)) Q-Eta
