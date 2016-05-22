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
wkv≼ (keep τ Γ₁≼Γ₂) vz = vz
wkv≼ (keep σ Γ₁≼Γ₂) (vs x) = vs (wkv≼ Γ₁≼Γ₂ x)
wkv≼ (drop τ₁ Γ₁≼Γ₂) x = vs (wkv≼ Γ₁≼Γ₂ x)

wkTm≼ : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Tm Γ₁ τ → Tm Γ₂ τ
wkTm≼ Γ₁≼Γ₂ (var x) = var (wkv≼ Γ₁≼Γ₂ x)
wkTm≼ Γ₁≼Γ₂ (app s t) = app (wkTm≼ Γ₁≼Γ₂ s) (wkTm≼ Γ₁≼Γ₂ t)
wkTm≼ Γ₁≼Γ₂ (Λ t) = Λ (wkTm≼ (keep _ Γ₁≼Γ₂) t)

--
-- Second, a hybrid of both machineries.
--
-- Caveat: it might be easier to use Shub from McBride's "Dependently-typed
-- metaprogramming in Agda", but I haven't tried. Also, that appears more general.
--

_conDiff_ : ∀ {Γ₁ Γ₂ τ} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) (x : Var Γ₁ τ) → (Γ₁ - x) ≼ (Γ₂ - wkv≼ Γ₁≼Γ₂ x)
∅ conDiff ()
keep τ Γ₁≼Γ₂ conDiff vz = Γ₁≼Γ₂
keep τ Γ₁≼Γ₂ conDiff vs x = keep τ (Γ₁≼Γ₂ conDiff x)
drop τ Γ₁≼Γ₂ conDiff vz = drop τ (Γ₁≼Γ₂ conDiff vz)
drop τ Γ₁≼Γ₂ conDiff vs x = drop τ (Γ₁≼Γ₂ conDiff (vs x))

-- Here, we allow substituting a term u defined in a bigger context into a term
-- in a smaller context.
subst≼ : ∀ {Γ₁ Γ₂ σ τ} → Tm Γ₁ τ → (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) → (x : Var Γ₁ σ) → Tm (Γ₂ - wkv≼ Γ₁≼Γ₂ x) σ → Tm (Γ₂ - wkv≼ Γ₁≼Γ₂ x) τ
subst≼ t Γ₁≼Γ₂ x u = subst (wkTm≼ Γ₁≼Γ₂ t) (wkv≼ Γ₁≼Γ₂ x) u

-- Here, we allow substituting a term u defined in a smaller context into a term
-- in a bigger context.
subst≼′ : ∀ {Γ₁ Γ₂ σ τ} → Tm Γ₂ τ → (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) → (x : Var Γ₁ σ) → Tm (Γ₁ - x) σ → Tm (Γ₂ - wkv≼ Γ₁≼Γ₂ x) τ
subst≼′ t Γ₁≼Γ₂ x u = subst t (wkv≼ Γ₁≼Γ₂ x) (wkTm≼ (Γ₁≼Γ₂ conDiff x) u)

mutual
  data Nf : Con → Ty → Set where
    λn : ∀ {Γ σ τ} → Nf (Γ , σ) τ → Nf Γ (σ ⇒ τ)
    ne : ∀ {Γ} → Ne Γ ○ → Nf Γ ○

  data Ne : Con → Ty → Set where
    _,_ : ∀ {Γ σ τ} → (v : Var Γ σ) → (s : Sp Γ σ τ) → Ne Γ τ

  -- Spines
  --A typed application context; Sp Γ σ τ has a hole of type σ and the context has type τ.

  data Sp : Con → Ty → Ty → Set where
    ε : ∀ {Γ σ} → Sp Γ σ σ
    _,_ : ∀ {Γ ρ σ τ} → (n : Nf Γ τ) → Sp Γ σ ρ → Sp Γ (τ ⇒ σ) ρ

-- Normal forms can be embedded into terms
mutual
  ⌈_⌉ : ∀ {Γ σ} → Nf Γ σ → Tm Γ σ
  ⌈ λn n ⌉ = Λ ⌈ n ⌉
  ⌈ ne n ⌉ = embNe n
  embNe : ∀ {Γ σ} → Ne Γ σ → Tm Γ σ
  embNe (v , s) = embSp s (var v)
  embSp : ∀ {Γ σ τ} → Sp Γ σ τ → Tm Γ σ → Tm Γ τ
  embSp ε acc = acc
  embSp (n , s) acc = embSp s (app acc ⌈ n ⌉)

mutual
  wkSp : ∀ {Γ ρ σ τ} → (x : Var Γ σ) → Sp (Γ - x) τ ρ → Sp Γ τ ρ
  wkSp x ε = ε
  wkSp x (n , s) = (wkNf x n) , (wkSp x s)

  wkNe : ∀ {Γ σ τ} → (x : Var Γ σ) → Ne (Γ - x) τ → Ne Γ τ
  wkNe x (v , s) = (wkv x v) , (wkSp x s)

  wkNf : ∀ {Γ σ τ} → (x : Var Γ σ) → Nf (Γ - x) τ → Nf Γ τ
  wkNf x (λn n) = λn (wkNf (vs x) n)
  wkNf x (ne n) = ne (wkNe x n)

-- apply the spine s to u, building the context for (app s u).
appSp : ∀ {Γ ρ σ τ} → Sp Γ ρ (σ ⇒ τ) → Nf Γ σ → Sp Γ ρ τ
appSp ε u = u , ε
appSp (n , s) u = n , appSp s u

-- η-expansion
mutual
  nvar : ∀ {σ Γ} → Var Γ σ → Nf Γ σ
  nvar x = ne2nf (x , ε)
  ne2nf : ∀ {σ Γ} → Ne Γ σ → Nf Γ σ
  ne2nf {○} n = ne n
  ne2nf {σ ⇒ τ} (v , s) = λn (ne2nf (vs v , appSp (wkSp vz s) (nvar vz)))

-- β-reduction
mutual
  _[_:=_] : ∀ {Γ σ τ} → Nf Γ τ → (x : Var Γ σ) → Nf (Γ - x) σ → Nf (Γ - x) τ
  λn n [ x := u ] = λn (n [ vs x := wkNf vz u ])
  ne (v , s) [ x := u ] with eq x v
  ne (v , s) [ .v := u ] | same = u ◇ (s < v := u >)
  ne (.(wkv x z) , s) [ x := u ] | diff .x z = ne (z , (s < x := u >))

  _<_:=_> : ∀ {Γ ρ σ τ} → Sp Γ τ ρ → (x : Var Γ σ) → Nf (Γ - x) σ → Sp (Γ - x) τ ρ
  ε < x := u > = ε
  (n , s) < x := u > = (n [ x := u ]) , (s < x := u >)

  _◇_ : ∀ {Γ σ τ} → Nf Γ σ → Sp Γ σ τ → Nf Γ τ
  nf ◇ ε = nf
  nf ◇ (n , s) = napp nf n ◇ s

  napp : ∀ {Γ σ τ} → Nf Γ (σ ⇒ τ) → Nf Γ σ → Nf Γ τ
  napp (λn n) u = n [ vz := u ]

nf : ∀ {Γ σ} → Tm Γ σ → Nf Γ σ
nf (var x) = nvar x
nf (app t₁ t₂) = napp (nf t₁) (nf t₂)
nf (Λ t) = λn (nf t)

-- Completeness
import Relation.Binary.PropositionalEquality as P
open P hiding (subst)
open P.≡-Reasoning

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

accSp : forall {Γ σ τ ρ} → (ts : Sp Γ ρ (σ ⇒ τ)) → (u : Nf Γ σ) → (acc : Tm Γ ρ) → embSp (appSp ts u) acc βη-≡ embSp (u , ε) (embSp ts acc)
accSp ε u acc = brefl
accSp (n , ts) u acc = accSp ts u (app acc ⌈ n ⌉)

congEmbSp : ∀ {Γ σ τ} → (s : Sp Γ σ τ) → {t₁ t₂ : Tm Γ σ} → t₁ βη-≡ t₂ → embSp s t₁ βη-≡ embSp s t₂
congEmbSp ε βη = βη
congEmbSp (n , s) βη = congEmbSp s (congApp βη brefl)
--wkNfTm : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → app (wkTm x t) ⌈ wkNf x n ⌉ βη-≡ wkTm x (embSp s (app t ⌈ n ⌉))
--wkNfTm : ∀ {Γ σ τ ρ} (x : Var Γ σ) t n → app (wkTm x t) ⌈ wkNf x n ⌉ βη-≡ wkTm x (app t ⌈ n ⌉)
mutual
  wkNfTm : ∀ {Γ σ τ} (x : Var Γ σ) (n : Nf (Γ - x) τ) → ⌈ wkNf x n ⌉ βη-≡ wkTm x ⌈ n ⌉
  wkNfTm x (λn n) = congΛ (wkNfTm (vs x) n)
  wkNfTm x (ne (v , s)) = wkSpTm x s (var v)
  wkSpTm : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → (s : Sp (Γ - x) τ ρ) → ∀ t → embSp (wkSp x s) (wkTm x t) βη-≡ wkTm x (embSp s t)
  wkSpTm x ε t = brefl
  wkSpTm x (n , s) t = btrans (congEmbSp (wkSp x s) (congApp brefl (wkNfTm x n))) (wkSpTm x s (app t ⌈ n ⌉))

mutual
  compNe : ∀ {σ Γ} (n : Ne Γ σ) → ⌈ ne2nf n ⌉ βη-≡ embNe n
  compNe {○} n = brefl
  compNe {σ ⇒ τ} (v , s) =
    btrans
      (congΛ
        (btrans
          (compNe (vs v , appSp (wkSp vz s) (nvar vz)))
          (btrans
            (accSp (wkSp vz s) (nvar vz) (var (vs v)))
            (congApp
              (wkSpTm vz s (var v))
              (compVar vz)))))
      eta
  compVar : ∀ {Γ σ} (v : Var Γ σ) → ⌈ nvar v ⌉ βη-≡ var v
  compVar v = compNe (v , ε)

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

congWkTm : forall {Γ σ τ} → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
congWkTm x brefl = brefl
congWkTm x (bsym βη) = bsym (congWkTm x βη)
congWkTm x (btrans βη βη₁) = btrans (congWkTm x βη) (congWkTm x βη₁)
congWkTm x (congΛ βη) = congΛ (congWkTm (vs x) βη)
congWkTm x (congApp βη βη₁) = congApp (congWkTm x βη) (congWkTm x βη₁)
congWkTm x beta = btrans beta {!!}
congWkTm x eta = btrans (congΛ (congApp {!!} brefl)) eta

congSubst : ∀ {Γ σ τ} (t : Tm Γ τ) (x : Var Γ σ) {u₁ u₂} → u₁ βη-≡ u₂ → subst t x u₁ βη-≡ subst t x u₂
congSubst (var x) x₁ βη = {!!}
congSubst (app s t) x βη = congApp (congSubst s x βη) (congSubst t x βη)
congSubst (Λ t) x βη = congΛ (congSubst t (vs x) (congWkTm vz βη))

mutual
  substEmbSp : ∀ {Γ σ τ ρ} → (ts : Sp Γ τ ρ) → (x : Var Γ σ) → (t : Nf (Γ - x) σ) → (acc : Tm Γ τ) → embSp (ts < x := t >) (subst acc x ⌈ t ⌉) βη-≡ subst (embSp ts acc) x ⌈ t ⌉
  substEmbSp ε x t acc = brefl
  substEmbSp (n , ts) x t acc =
    btrans
      (congEmbSp (ts < x := t >) (congApp brefl (substNfSubst n x t)))
      (substEmbSp ts x t (app acc ⌈ n ⌉))

  appNfEmbSp : ∀ {Γ σ} → (u : Nf Γ σ) → (ts : Sp Γ σ ○) → ⌈ u ◇ ts ⌉ βη-≡ embSp ts ⌈ u ⌉
  appNfEmbSp u ε = brefl
  appNfEmbSp u (n , ts) = btrans (appNfEmbSp (napp u n) ts) (congEmbSp ts (compApp u n))

  substNfSubst : ∀ {Γ σ τ} →
    (t : Nf Γ τ) → (x : Var Γ σ) → (u : Nf (Γ - x) σ) →
    ⌈ t [ x := u ] ⌉ βη-≡ subst ⌈ t ⌉ x ⌈ u ⌉
  substNfSubst (λn n) x u =
    congΛ (btrans
      (substNfSubst n (vs x) (wkNf vz u))
      (congSubst ⌈ n ⌉ (vs x) (wkNfTm vz u)))
  substNfSubst (ne (v , s)) x u with eq x v | inspect (eq x) v
  substNfSubst (ne (v , s)) .v u | same | [ eq ] = btrans (appNfEmbSp u (s < v := u >))
    (P.subst (λ □ → embSp (s < v := u >) □ βη-≡ subst (embSp s (var v)) v ⌈ u ⌉)
      (substVarSame v ⌈ u ⌉)
      (substEmbSp s v u (var v)))
  substNfSubst (ne (.(wkv x z) , s)) x u | diff .x z | _ = {!!}

  compApp : ∀ {Γ σ τ} → (t₁ : Nf Γ (σ ⇒ τ)) → (t₂ : Nf Γ σ) → ⌈ napp t₁ t₂ ⌉ βη-≡ app ⌈ t₁ ⌉ ⌈ t₂ ⌉
  compApp (λn t₁) t₂ = btrans (substNfSubst t₁ vz t₂) (bsym (beta {t = ⌈ t₁ ⌉} {u = ⌈ t₂ ⌉}))

completeness : ∀ {Γ σ} (t : Tm Γ σ) → ⌈ nf t ⌉ βη-≡ t
completeness (var x) = compVar x
completeness (app t₁ t₂) = btrans (compApp (nf t₁) (nf t₂)) (congApp (completeness t₁) (completeness t₂))
completeness (Λ t) = congΛ (completeness t)

-- soundness : ∀ {Γ σ} {t u : Tm Γ σ} → t βη-≡ u → nf t ≡ nf u
-- soundness = {!!}

-- brefl′ : ∀ {Γ σ} {t₁ t₂ : Tm Γ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
-- brefl′ refl = brefl

-- -- How I would define completeness, as the inverse of soundness.
-- completeness′ : ∀ {Γ σ} {t u : Tm Γ σ} → nf t ≡ nf u → t βη-≡ u
-- completeness′ {t = t} {u = u} nf-t≡nf-u =
--   btrans (bsym (completeness t)) -- t βη-≡ ⌈ nf t ⌉
--     (btrans (brefl′ (cong ⌈_⌉ nf-t≡nf-u)) -- Since nf t ≡ nf u, then ⌈ nf t ⌉ ≡ ⌈ nf u ⌉
--     (completeness u)) -- ⌈ nf u ⌉ βη-≡ u
