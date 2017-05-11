module EquivSubst1 where
open import Term
open import Subst1

-- Derivations of βη-equalities.
-- CHALLENGE: try to prove that such derivations can be weakened (wkβη-≡).
--
-- Most of the trouble seems to arise from representing object-level typing
-- contexts in an intrinsically typed way. It seems proofs might be easier on
-- representations *without* such intrinsic typing. In fact, the easiest way to
-- do proofs on this intrinsically typed representation might be to relate it to
-- the representation without intrinsic typing. Since operations are not
-- type-directed, we would not even need to define extrinsic typing there.
--
-- Since the Q-Eta uses weakening, we need to prove that the weakening we're
-- applying to the substitution commutes (somehow) with the weakening used by
-- Q-Eta. Similarly, for Q-Beta we need to relate the weakening we apply to the
-- derivation to the substitution.
--
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

-- Try to
-- Attempt (1): Try to prove that we can swap weakenings, up to βη-equality.
wkCommStmβ : ∀ {Γ τ σ σ₁} → (x : Var Γ σ) → (y : Var (Γ - x) σ₁) (t : Tm (Γ - x - y) τ) → Set
wkCommStmβ {Γ} {τ} {σ} {σ₁} x y t with swapCtx _ _ _ x y | swapCtxT x y t
-- Terms t and t' are "equal", but they have different types, so stating their propositional equality
-- requires using P.subst p for a cast. So t′≡t has type t′ ≡ P.subst (λ □ → Tm □ .τ) p t, as given by swapCtxT.
-- And we need to use t' in the statement.
--
-- One problem is that we need equivalence
--   Γ - x - y ≡ Γ - wkv x y - swap x y
--
-- Lemma swapCtx _ _ _ x y proves that, but we can't match such a proof against
-- refl, because we can't unify Γ - x - y and Γ - wkv x y - swap x y.
-- As a consequence, the use of P.subst won't reduce.
--
-- The same problem applies to wkComm in attempt (2).
--
-- In wkCommH we avoid P.subst through heterogeneous equality, but we still run
-- into trouble.
--
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

-- Attempt (2): Try to prove that we can swap weakenings, up to heterogeneous
-- equality. But we use propositional equality by calling swapCtxT, which is
-- silly. This silliness is fixed in Attempt (3) below.
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

-- Attempt (3): Try to prove that we can swap weakenings, up to heterogeneous equality.
wkCommStmH : ∀ {Γ τ σ σ₁} → (x : Var Γ σ) → (y : Var (Γ - x) σ₁) (t : Tm (Γ - x - y) τ) → Set
wkCommStmH x y t with swapCtxTH x y t
... | t′ , t≅t′ =
    wkTm (wkv x y) (wkTm (swap x y) t′)
  ≅
    wkTm x (wkTm y t)

wkCommH : ∀ {Γ τ σ σ₁} → (x : Var Γ σ) → (y : Var (Γ - x) σ₁) (t : Tm (Γ - x - y) τ) →
  wkCommStmH x y t
wkCommH x y t with swapCtxTH x y t
wkCommH vz y (var x) | _ , refl = refl
wkCommH vz y (app s t) | _ , refl = H.cong₂ app (wkCommH vz y s) (wkCommH vz y t)
wkCommH vz y (Λ t) | _ , refl = H.cong Λ (wkCommH (vs vz) (vs y) t)
wkCommH vz y (c k) | _ , refl = refl
wkCommH (vs x) vz (var x₁) | _ , refl = refl
wkCommH (vs x) vz (app s t) | _ , refl = H.cong₂ app (wkCommH (vs x) vz s) (wkCommH (vs x) vz t)
wkCommH (vs x) vz (Λ t) | _ , refl = H.cong Λ (wkCommH (vs (vs x)) (vs vz) t)
wkCommH (vs x) vz (c k) | _ , refl = refl
--
-- Probably we don't really need to case split on x and y, except for the
-- variable case. This lemma must be proven just by induction on terms.
-- To wit, it seems that wkCommH2 is as successful
-- as wkCommH.
--
-- But because of typing issues I'm discussing, I don't know how to exploit
-- t≅t′. I can only use it if I split on x and y, and even then not in the case
-- for (vs x) (vs y).
--
-- Here we cannot match on t≅t′, as that would still try unifying (.Γ - x - y ,
-- .τ) and (.Γ - wkv x y - swap x y , .τ). So no computation on t′ can reduce
-- directly, and it's not clear how to reduce it indirectly.
wkCommH {Γ , σ} {τ} (vs x) (vs y) (var x₁) | t′ , t≅t′ with swapCtx _ _ (Γ , σ) (vs x) (vs y)
-- Here, a proof of reduce-wkTm-t′ reduces to a similar lemma for variables, probably provable.
... | p = H.trans reduce-wkTm-t′ (H.cong var {!!})
  where
    -- wkTm x (var v) = var (wkv x v)
    x₁′ : Var (Γ - wkv x y - swap x y , σ) τ
    x₁′ rewrite P.sym p = x₁
    -- We know t≅t′ : t′ ≅ var x₁. If t′ were definitionally equal to var x₁, a
    -- definitional equality similar to reduce-wkTm-t′ would follow. Let's state it as a separate lemma.
    -- Not clear how to prove it.
    reduce-wkTm-t′ : wkTm (vs (wkv x y)) (wkTm (vs (swap x y)) t′) ≅ var (wkv (vs (wkv x y)) (wkv (vs (swap x y)) x₁′))
    reduce-wkTm-t′ = {!!}
wkCommH (vs x) (vs y) (app s t) | t′ , t≅t′ = H.trans {!!} (H.cong₂ app (wkCommH (vs x) (vs y) s) (wkCommH (vs x) (vs y) t))
wkCommH (vs x) (vs y) (Λ t) | t′ , t≅t′ = H.trans {!!} (H.cong Λ (wkCommH (vs (vs x)) (vs (vs y)) t))
wkCommH (vs x) (vs y) (c k) | t′ , t≅t′ = {!!}

wkCommH2 : ∀ {Γ τ σ σ₁} → (x : Var Γ σ) → (y : Var (Γ - x) σ₁) (t : Tm (Γ - x - y) τ) →
  wkCommStmH x y t
wkCommH2 x y t with swapCtxTH x y t
wkCommH2 {Γ} {τ} x y (var x₁) | t′ , t≅t′ with swapCtx _ _ _ x y
... | p = H.trans reduce-wkTm-t′ (H.cong var {!!})
  where
    -- wkTm x (var v) = var (wkv x v)
    x₁′ : Var (Γ - wkv x y - swap x y) τ
    x₁′ rewrite P.sym p = x₁
    -- We know t≅t′ : t′ ≅ var x₁. If t′ were definitionally equal to var x₁, a
    -- definitional equality similar to reduce-wkTm-t′ would follow. Let's state it as a separate lemma.
    -- Not clear how to prove it.
    reduce-wkTm-t′ : wkTm (wkv x y) (wkTm (swap x y) t′) ≅ var (wkv (wkv x y) (wkv (swap x y) x₁′))
    reduce-wkTm-t′ = {!!}
wkCommH2 x y (app s t) | t′ , t≅t′ = H.trans {!!} (H.cong₂ app (wkCommH x y s) (wkCommH x y t))
wkCommH2 x y (Λ t) | t′ , t≅t′ = H.trans {!!} (H.cong Λ (wkCommH2 (vs x) (vs y) t))
wkCommH2 x y (c k) | t′ , t≅t′ = {!!}

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
wkSubstR : ∀ {Γ σ σ₁ τ} → (x : Var Γ σ) → (t : Tm ((Γ - x), σ₁) τ) → (u : Tm (Γ - x) σ₁) → subst (wkTm (vs x) t) vz (wkTm x u) βη-≡ wkTm x (subst t vz u)
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
