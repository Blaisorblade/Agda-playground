{-# OPTIONS --allow-unsolved-metas #-}
open import Term
open import Subst2

infix 10 _βη-≡_

data _βη-≡_ : ∀ {Γ σ} → Tm Γ σ → Tm Γ σ → Set where
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
    app (Λ t) u βη-≡ subst vz u t

{-
  Q-Eta : ∀ {Γ σ τ} {t : Tm Γ (σ ⇒ τ)} →
    Λ (app (wkTm vz t) (var vz)) βη-≡ t
    -}

  Q-Ext :
    ∀ {Γ σ τ} {x} {s t : Tm (Γ - x) (σ ⇒ τ)} →
    app (wkTm′ x s) (var x) βη-≡ app (wkTm′ x t) (var x) →
    s βη-≡ t

open import Data.List

wkr′ : ∀ {Γ Δ σ} → (x : Var Γ σ) → Ren (Γ - x) Δ → Ren Γ (Δ , σ)
wkr′ x r y with eq x y
wkr′ x r .x | same = vz
wkr′ x r .((_ /= x) z) | diff .x z = vs (r z)

wkθ′ : ∀ {Γ Δ σ} → (x : Var Γ σ) → Shub (Γ - x) Δ → Shub Γ (Δ , σ)
wkθ′ = {!!}

{-
shubComm : ∀ {Γ Δ Ξ τ} → (θ₁ : Shub Γ Δ) → (θ₂ : Shub Δ Ξ) → (t : Tm Γ τ) → θ₂ // (θ₁ // t) βη-≡ {!!}
shubComm = {!!}
-}
{-
shubComm : ∀ {Γ Δ σ τ} → (x : Var Γ σ) (u : Tm (Γ - x) σ) (θ : Shub (Γ - x) Δ) → (t : Tm Γ τ) →
  {! sub (atomicSubst {!x!} (θ // u)) !} // {!wkθ σ θ!} // t
 βη-≡
   θ // sub (atomicSubst x u) // t
   -}

{-
open import Relation.Binary.PropositionalEquality hiding (subst)
shubFoo : ∀ {Γ Δ τ} → (θ : Shub Γ Δ) → (θ (τ ∷ []) vz) ≡ var vz
shubFoo = {!!}


shubComm : ∀ {Γ Δ σ τ} (θ : Shub Γ Δ) (u : Tm Γ σ) → (t : Tm (Γ , σ) τ) →
   sub (atomicSubst vz (θ // u))  // wkθ σ θ // t
 βη-≡
   θ // sub (atomicSubst vz u) // t
shubComm θ u (var x) with eq vz x
shubComm θ u (var .vz) | same = {!!}
shubComm θ u (var .(vs z)) | diff .vz z = {!!}
shubComm θ u (app s t) = Q-App (shubComm θ u s) (shubComm θ u t)
shubComm θ u (Λ t) = Q-Abs {!shubComm!}
shubComm θ u (c k) = Q-Refl
-}

substRenComm : ∀ {Γ Δ σ τ} (r : Ren Γ Δ) (u : Tm Γ σ) → (t : Tm (Γ , σ) τ) →
   sub (atomicSubst vz (ren r // u))  // ren (wkr r) // t
 βη-≡
   ren r // sub (atomicSubst vz u) // t
--substRenComm r = shubComm (ren r)
substRenComm r u (var vz) = Q-Refl
substRenComm r u (var (vs x)) = Q-Refl
substRenComm r u (app s t) = Q-App (substRenComm r u s) (substRenComm r u t)
substRenComm r u (Λ t) = Q-Abs {!substRenComm!}
substRenComm r u (c k) = Q-Refl


{-
wkSubst : ∀ {Γ Δ τ} → (θ : Sub Γ Δ) → (t : Tm Γ τ) → {!? βη-≡ wkTm θ!}
wkSubst = {!!}
-}


wkβη-≡ : ∀ {Γ Δ τ} (r : Ren Γ Δ) {t₁ t₂ : Tm Γ τ} → t₁ βη-≡ t₂ → wkTm r t₁ βη-≡ wkTm r t₂
wkβη-≡ r Q-Refl = Q-Refl
wkβη-≡ r (Q-Symm Eq) = Q-Symm (wkβη-≡ r Eq)
wkβη-≡ r (Q-Trans Eq Eq₁) = Q-Trans (wkβη-≡ r Eq) (wkβη-≡ r Eq₁)
wkβη-≡ r (Q-Abs Eq) = Q-Abs (wkβη-≡ (wkr r) Eq)
wkβη-≡ r (Q-App Eq Eq₁) = Q-App (wkβη-≡ r Eq) (wkβη-≡ r Eq₁)
wkβη-≡ r (Q-Beta {t = t} {u = u}) = Q-Trans Q-Beta (substRenComm r u t)
wkβη-≡ r {.s} {.t} (Q-Ext {x = x} {s = s} {t = t} Eq) =
  let r′ = wkr′ x r in
  Q-Ext {x = {!r′ x!}} {s = {!!}} {t = {!!}} {!!}
    --  Q-Ext {x = r′ x} {s = ren {!!} // s} {t = ren {!!} // t} {!wkβη-≡ ? Eq!}



{-
shubβη-≡ : ∀ {Γ Δ τ} (θ : Shub Γ Δ) {t₁ t₂ : Tm Γ τ} → t₁ βη-≡ t₂ → θ // t₁ βη-≡ θ // t₂
shubβη-≡ θ Q-Refl = Q-Refl
shubβη-≡ θ (Q-Symm Eq) = Q-Symm (shubβη-≡ θ Eq)
shubβη-≡ θ (Q-Trans Eq Eq₁) = Q-Trans (shubβη-≡ θ Eq) (shubβη-≡ θ Eq₁)
shubβη-≡ θ (Q-Abs {σ = σ} Eq) = Q-Abs (shubβη-≡ (wkθ σ θ) Eq)
shubβη-≡ θ (Q-App Eq Eq₁) = Q-App (shubβη-≡ θ Eq) (shubβη-≡ θ Eq₁)
shubβη-≡ θ (Q-Beta {t = t} {u = u}) = Q-Trans Q-Beta (shubComm u θ t)
shubβη-≡ θ (Q-Ext {x = x} {s = s} {t = t} Eq) = Q-Ext {x = {!(wkθ′ x θ) [] x!}} {s = s} {t = t} {!!}
-}
