{-# OPTIONS --rewriting --allow-unsolved-metas #-}
module AMSz where

open import Lib hiding (id; _∘_)
--import II as S
open import II using (PS; P; S)
import IIA as S

infixl 7 _[_]TS
infixl 7 _[_]TP
infixl 7 _[_]T
infix  6 _∘_
infixl 8 _[_]tS
infixl 8 _[_]tP
infixl 8 _[_]t
infixl 5 _,sS_
infixl 5 _,sP_
infixl 5 _,s_
infixl 3 _▶_
infixl 3 _▶S_
infixl 3 _▶P_

record Con : Set₂ where
  field
    ᴬ   : Set₁
    ᴹ   : ᴬ → ᴬ → Set₁
    sz  : S.Con
    Cod : S.Tm sz S.U
    Dec : S.Tm sz (S.Π Cod S.U)
    
record TyS (Γ : Con) : Set₂ where
  module Γ = Con Γ
  field
    ᴬ   : Γ.ᴬ → Set₁
    ᴹ   : ∀{γᴬ δᴬ} → Γ.ᴹ γᴬ δᴬ → ᴬ γᴬ → ᴬ δᴬ → Set
    sz  : S.Ty Γ.sz

record TyP (Γ : Con) : Set₂ where
  module Γ = Con Γ
  field
    ᴬ   : Γ.ᴬ → Set
    ᴹ   : ∀{γᴬ δᴬ} → Γ.ᴹ γᴬ δᴬ → ᴬ γᴬ → ᴬ δᴬ → Set₁
    sz  : S.Ty Γ.sz

Ty : (Γ : Con) (k : PS) → Set₂
Ty Γ P = TyP Γ
Ty Γ S = TyS Γ

record TmS (Γ : Con) (B : TyS Γ) : Set₂ where
  module Γ = Con Γ
  module B = TyS B
  field
    ᴬ   : (γᴬ : Γ.ᴬ) → B.ᴬ γᴬ
    ᴹ   : ∀{γᴬ δᴬ}(γᴹ : Γ.ᴹ γᴬ δᴬ) → B.ᴹ γᴹ (ᴬ γᴬ) (ᴬ δᴬ)
    sz  : S.Tm Γ.sz B.sz

record TmP (Γ : Con) (A : TyP Γ) : Set₂ where
  module Γ = Con Γ
  module A = TyP A
  field
    ᴬ   : (γᴬ : Γ.ᴬ) → A.ᴬ γᴬ
    ᴹ   : ∀{γᴬ δᴬ}(γᴹ : Γ.ᴹ γᴬ δᴬ) → A.ᴹ γᴹ (ᴬ γᴬ) (ᴬ δᴬ)
    sz  : S.Tm Γ.sz A.sz

Tm : {k : PS} → (Γ : Con) → (A : Ty Γ k) → Set₂
Tm {P} = TmP
Tm {S} = TmS

record Sub (Γ : Con) (Δ : Con) : Set₂ where
  module Γ = Con Γ
  module Δ = Con Δ
  field
    ᴬ   : Γ.ᴬ → Δ.ᴬ
    ᴹ   : ∀{γᴬ δᴬ} → Γ.ᴹ γᴬ δᴬ → Δ.ᴹ (ᴬ γᴬ) (ᴬ δᴬ)
    sz  : S.Sub Γ.sz Δ.sz
    Cod : ∀ γ → (Δ.Cod S.[ sz ]t) γ ≡ Γ.Cod γ
    Dec : ∀ γ α → (Δ.Dec S.[ sz ]t) γ α ≡ Γ.Dec γ (coe (Cod γ) α)

∙ : Con
∙ = record { ᴬ   = Lift _ ⊤ ;
             ᴹ   = λ _ _ → Lift _ ⊤ ;
             sz  = S.∙ S.▶ S.U S.▶ S.Π S.vz S.U ;
             Cod = S.vs S.vz ;
             Dec = S.vz }

_▶S_ : (Γ : Con) → TyS Γ → Con
Γ ▶S B = record { ᴬ   = Σ Γ.ᴬ B.ᴬ ;
                  ᴹ   = λ { (γᴬ , αᴬ) (δᴬ , βᴬ) → Σ (Γ.ᴹ γᴬ δᴬ) λ γᴹ → B.ᴹ γᴹ αᴬ βᴬ } ;
                  sz  = Γ.sz S.▶ B.sz ;
                  Cod = S.vs Γ.Cod ;
                  Dec = S.vs Γ.Dec }
  where
    module Γ = Con Γ
    module B = TyS B

_▶P_ : (Γ : Con) → TyP Γ → Con
Γ ▶P A = record { ᴬ   = Σ Γ.ᴬ A.ᴬ ;
                  ᴹ   = λ { (γᴬ , αᴬ) (δᴬ , βᴬ) → Σ (Γ.ᴹ γᴬ δᴬ) λ γᴹ → A.ᴹ γᴹ αᴬ βᴬ } ;
                  sz  = Γ.sz S.▶ A.sz ;
                  Cod = S.vs Γ.Cod ;
                  Dec = S.vs Γ.Dec }
  where
    module Γ = Con Γ
    module A = TyP A

_▶_ : ∀{k}(Γ : Con) → (A : Ty Γ k) → Con
_▶_ {P} Γ A = Γ ▶P A
_▶_ {S} Γ A = Γ ▶S A

U : {Γ : Con} → TyS Γ
U {Γ} = record { ᴬ   = λ γ → Set ;
                 ᴹ   = λ γᴹ γᴬ δᴬ → γᴬ → δᴬ ;
                 sz  = S.El Γ.Cod }
  where
    module Γ = Con Γ

El : {Γ : Con} (a : TmS Γ U) → TyP Γ
El {Γ} a = record { ᴬ   = λ γᴬ → a.ᴬ γᴬ ;
                    ᴹ   = λ γᴹ αᴬ βᴬ → Lift _ (a.ᴹ γᴹ αᴬ ≡ βᴬ) ;
                    sz  = S.El (Γ.Dec S.$ a.sz) }
  where
    module Γ = Con Γ
    module a = TmS a

-- Internal function type
ΠS : {Γ : Con} (a : TmS Γ U) (B : TyS (Γ ▶P El a)) → TyS Γ
ΠS {Γ} a B = record { ᴬ   = λ γᴬ → (α : a.ᴬ γᴬ) → B.ᴬ (γᴬ , α) ;
                      ᴹ   = λ {γᴬ} γᴹ πᴬ ϕᴬ → (αᴬ : a.ᴬ γᴬ)→ B.ᴹ (γᴹ , lift refl) (πᴬ αᴬ) (ϕᴬ (a.ᴹ γᴹ αᴬ)) ;
                      sz  = S.Π (Γ.Dec S.$ a.sz) B.sz }
  where
    module Γ = Con Γ
    module a = TmS a
    module B = TyS B

ΠP : {Γ : Con} (a : TmS Γ U) (A : TyP (Γ ▶P El a)) → TyP Γ
ΠP {Γ} a A = record { ᴬ   = λ γᴬ → (α : a.ᴬ γᴬ) → A.ᴬ (γᴬ , α) ;
                      ᴹ   = λ {γᴬ} γᴹ πᴬ ϕᴬ → (αᴬ : a.ᴬ γᴬ) → A.ᴹ (γᴹ , lift refl) (πᴬ αᴬ) (ϕᴬ (a.ᴹ γᴹ αᴬ)) ;
                      sz  = S.Π (Γ.Dec S.$ a.sz) A.sz }
  where
    module a = TmS a
    module A = TyP A
    module Γ = Con Γ

Π : ∀{k}{Γ : Con} → (a : TmS Γ U) → (B : Ty (Γ ▶ El a) k) → Ty Γ k
Π {P} a B = ΠP a B
Π {S} a B = ΠS a B

appS : {Γ : Con} {a : TmS Γ U} → {B : TyS (Γ ▶P El a)} → (f : TmS Γ (ΠS a B)) → TmS (Γ ▶P El a) B
appS {Γ}{a}{B} f = record { ᴬ   = λ { (γ , α) → f.ᴬ γ α } ;
                            ᴹ   = λ { {γᴬ , αᴬ} {δᴬ , βᴬ} (γᴹ , lift refl) → (f.ᴹ γᴹ αᴬ) } ;
                            sz  = S.app f.sz }
  where
    module a = TmS a
    module B = TyS B
    module f = TmS f
    module Γ = Con Γ

appP : {Γ : Con} {a : TmS Γ U} → {B : TyP (Γ ▶P El a)} → (f : TmP Γ (ΠP a B)) → TmP (Γ ▶P El a) B
appP {a = a}{B} f = record { ᴬ   = λ { (γ , α) → f.ᴬ γ α } ;
                             ᴹ   = λ { {γᴬ , αᴬ} {δᴬ , βᴬ} (γᴹ , lift refl) → (f.ᴹ γᴹ αᴬ) } ;
                             sz  = S.app f.sz }
  where
    module a = TmS a
    module B = TyP B
    module f = TmP f

app : {k : PS}{Γ : Con}{a : TmS Γ U}{B : Ty (Γ ▶P El a) k} → (f : Tm Γ (Π a B)) → Tm (Γ ▶P El a) B
app {P} = appP
app {S} = appS

--External function type
Π̂S : {Γ : Con} (T : Set) (B : T → TyS Γ) → TyS Γ
Π̂S T B = record { ᴬ   = λ γᴬ → (τ : T) → TyS.ᴬ (B τ) γᴬ ;
                  ᴹ   = λ γᴹ πᴬ ϕᴬ → (τ : T) → TyS.ᴹ (B τ) γᴹ (πᴬ τ) (ϕᴬ τ) ;
                  sz  = S.Π̂ T λ τ → TyS.sz (B τ) }

Π̂P : {Γ : Con} (T : Set) (A : T → TyP Γ) → TyP Γ
Π̂P T A = record { ᴬ  = λ γᴬ → (τ : T) → TyP.ᴬ (A τ) γᴬ;
                  ᴹ  = λ γᴹ πᴬ ϕᴬ → (τ : T) → TyP.ᴹ (A τ) γᴹ (πᴬ τ) (ϕᴬ τ) ;
                  sz = S.Π̂ T λ τ → TyP.sz (A τ) }

Π̂ : {k : PS}{Γ : Con}(T : Set)(A : T → Ty Γ k) → Ty Γ k
Π̂ {P} = Π̂P
Π̂ {S} = Π̂S

âppS : {Γ : Con} {T : Set} {B : T → TyS Γ} (f : TmS Γ (Π̂S T B)) (τ : T) → TmS Γ (B τ)
âppS {Γ}{T}{B} f τ = record { ᴬ  = λ γᴬ → f.ᴬ γᴬ τ ;
                              ᴹ  = λ γᴹ → f.ᴹ γᴹ τ ;
                              sz = f.sz S.$̂ τ }
  where
    module f = TmS f
    module Γ = Con Γ

âppP : {Γ : Con} {T : Set} {B : T → TyP Γ} (f : TmP Γ (Π̂P T B)) (τ : T) → TmP Γ (B τ)
âppP {Γ}{T}{B} f τ = record { ᴬ  = λ γᴬ → f.ᴬ γᴬ τ ;
                              ᴹ  = λ γᴹ → f.ᴹ γᴹ τ ;
                              sz = f.sz S.$̂ τ }
  where
    module f = TmP f

âpp : {k : PS} {Γ : Con} {T : Set} {B : T → Ty Γ k} (f : Tm Γ (Π̂ T B)) (τ : T) → Tm Γ (B τ)
âpp {P} = âppP
âpp {S} = âppS

id : ∀{Γ} → Sub Γ Γ
id {Γ} = record { ᴬ   = λ γ → γ ;
                  ᴹ   = λ γᴹ → γᴹ ;
                  sz  = S.id ;
                  Cod = λ γ → refl ;
                  Dec = λ γ α → refl }

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
σ ∘ δ = record { ᴬ   = λ γ → σ.ᴬ (δ.ᴬ γ) ;
                 ᴹ   = λ γᴹ → σ.ᴹ (δ.ᴹ γᴹ) ;
                 sz  = σ.sz S.∘ δ.sz ;
                 Cod = λ γ → σ.Cod (δ.sz γ) ◾ δ.Cod γ ;
                 Dec = λ γ α → σ.Dec (δ.sz γ) α
                               ◾ δ.Dec γ (coe (σ.Cod (δ.sz γ)) α)
                               ◾ δ.Γ.Dec γ & coe∘ (δ.Cod γ) (σ.Cod (δ.sz γ)) α }
  where
    module σ = Sub σ
    module δ = Sub δ

_[_]TS : ∀{Γ Δ} → TyS Δ → Sub Γ Δ → TyS Γ
_[_]TS B σ = record { ᴬ   = λ γ → B.ᴬ (σ.ᴬ γ) ;
                      ᴹ   = λ γᴹ αᴬ βᴬ → B.ᴹ (σ.ᴹ γᴹ) αᴬ βᴬ ;
                      sz  = B.sz S.[ σ.sz ]T }
  where
    module B = TyS B
    module σ = Sub σ

_[_]TP : ∀{Γ Δ} → TyP Δ → Sub Γ Δ → TyP Γ
_[_]TP A σ = record { ᴬ   = λ γ → A.ᴬ (σ.ᴬ γ) ;
                      ᴹ   = λ γᴹ αᴬ βᴬ → A.ᴹ (σ.ᴹ γᴹ) αᴬ βᴬ ;
                      sz  = A.sz S.[ σ.sz ]T }
  where
    module A = TyP A
    module σ = Sub σ

_[_]T : ∀{k Γ Δ} → Ty Δ k → Sub Γ Δ → Ty Γ k
_[_]T {P} = _[_]TP
_[_]T {S} = _[_]TS

_[_]tS : ∀{Γ Δ}{A : TyS Δ} → TmS Δ A → (σ : Sub Γ Δ) → TmS Γ (A [ σ ]TS)
_[_]tS {Γ}{Δ}{A} a σ = record { ᴬ   = λ γ → a.ᴬ (σ.ᴬ γ) ;
                                ᴹ   = λ γᴹ → a.ᴹ (σ.ᴹ γᴹ) ;
                                sz  = a.sz S.[ σ.sz ]t }
  where
    module A = TyS A
    module a = TmS a
    module σ = Sub σ

_[_]tP : ∀{Γ Δ}{A : TyP Δ} → TmP Δ A → (σ : Sub Γ Δ) → TmP Γ (A [ σ ]TP)
_[_]tP {Γ}{Δ}{A} a σ = record { ᴬ   = λ γ → a.ᴬ (σ.ᴬ γ) ;
                                ᴹ   = λ γᴹ → a.ᴹ (σ.ᴹ γᴹ) ;
                                sz  = a.sz S.[ σ.sz ]t }
  where
    module A = TyP A
    module a = TmP a
    module σ = Sub σ

_[_]t : ∀{k Γ Δ}{A : Ty Δ k} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {P} = _[_]tP
_[_]t {S} = _[_]tS

ε : ∀{Γ} → Sub Γ ∙
ε {Γ} = record { ᴬ   = λ _ → lift tt ;
                 ᴹ   = λ _ → lift tt ;
                 sz  = S.ε S.,s Γ.Cod S.,s Γ.Dec ;
                 Cod = λ γ → refl ;
                 Dec = λ γ α → refl }
  where
    module Γ = Con Γ

_,sS_  : ∀{Γ Δ}(σ : Sub Γ Δ){B : TyS Δ} → TmS Γ (B [ σ ]TS) → Sub Γ (Δ ▶S B)
σ ,sS t = record { ᴬ   = λ γ → σ.ᴬ γ , t.ᴬ γ ;
                   ᴹ   = λ γᴹ → σ.ᴹ γᴹ , t.ᴹ γᴹ ;
                   sz  = σ.sz S.,s t.sz ;
                   Cod = λ γ → σ.Cod γ ;
                   Dec = λ γ α → σ.Dec γ α }
  where
    module σ = Sub σ
    module t = TmS t

_,sP_ : ∀{Γ Δ}(σ : Sub Γ Δ) → {A : TyP Δ} → (t : TmP Γ (A [ σ ]TP)) → Sub Γ (Δ ▶P A)
_,sP_ σ {A} t = record { ᴬ   = λ γ → σ.ᴬ γ , t.ᴬ γ ;
                         ᴹ   = λ γᴹ → σ.ᴹ γᴹ , t.ᴹ γᴹ ;
                         sz  = σ.sz S.,s t.sz ;
                         Cod = λ γ → σ.Cod γ ;
                         Dec = λ γ α → σ.Dec γ α }
  where
    module σ = Sub σ
    module A = TyP A
    module t = TmP t

_,s_ : ∀{k Γ Δ}(σ : Sub Γ Δ){A : Ty Δ k} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
_,s_ {P} = _,sP_
_,s_ {S} = _,sS_

π₁S : ∀{Γ Δ}{A : TyS Δ} → Sub Γ (Δ ▶S A) → Sub Γ Δ
π₁S σ = record { ᴬ   = λ γ → ₁ (σ.ᴬ γ) ;
                 ᴹ   = λ γᴹ → ₁ (σ.ᴹ γᴹ) ;
                 sz  = S.π₁ σ.sz ;
                 Cod = λ γ → σ.Cod γ ;
                 Dec = λ γ α → σ.Dec γ α }
  where
    module σ = Sub σ

π₁P : ∀{Γ Δ}{A : TyP Δ} → Sub Γ (Δ ▶P A) → Sub Γ Δ
π₁P σ = record { ᴬ   = λ γ → ₁ (σ.ᴬ γ) ;
                 ᴹ   = λ γᴹ → ₁ (σ.ᴹ γᴹ) ;
                 sz  = S.π₁ σ.sz ;
                 Cod = λ γ → σ.Cod γ ;
                 Dec = λ γ α → σ.Dec γ α }
  where
    module σ = Sub σ

π₁ : ∀{k}{Γ Δ}{A : Ty Δ k} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ {P} = π₁P
π₁ {S} = π₁S

π₂S : ∀{Γ Δ}{A : TyS Δ}(σ : Sub Γ (Δ ▶S A)) → TmS Γ (A [ π₁S σ ]TS)
π₂S {Γ}{Δ}{A} σ = record { ᴬ   = λ γ → ₂ (σ.ᴬ γ) ;
                           ᴹ   = λ γᴹ → ₂ (σ.ᴹ γᴹ) ;
                           sz  = S.π₂ σ.sz }
  where
    module σ = Sub σ

π₂P : ∀{Γ Δ}{A : TyP Δ}(σ : Sub Γ (Δ ▶P A)) → TmP Γ (A [ π₁P σ ]TP)
π₂P {Γ}{Δ}{A} σ = record { ᴬ   = λ γ → ₂ (σ.ᴬ γ) ;
                           ᴹ   = λ γ → ₂ (σ.ᴹ γ) ;
                           sz  = S.π₂ σ.sz }
  where
    module A = TyP A
    module σ = Sub σ

π₂ : ∀{k Γ Δ}{A : Ty Δ k}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ {k} σ ]T)
π₂ {P} = π₂P
π₂ {S} = π₂S

wk : ∀{k Γ}{A : Ty Γ k} → Sub (Γ ▶ A) Γ
wk {k} = π₁ {k} id

vz : ∀{k Γ}{A : Ty Γ k} → Tm (Γ ▶ A) (A [ wk {k} ]T)
vz = π₂ id

vsS : ∀{k Γ}{A : TyS Γ}{B : Ty Γ k} → TmS Γ A → TmS (Γ ▶ B) (A [ wk {k} ]TS)
vsS {k} t = t [ wk {k} ]tS

vsP : ∀{k Γ}{A : TyP Γ}{B : Ty Γ k} → TmP Γ A → TmP (Γ ▶ B) (A [ wk {k} ]TP)
vsP {k} t = t [ wk {k} ]tP

-- First kind: What is the resulting kind? Second kind: Along what kind are we weakening?
vs : ∀{k l Γ}{A : Ty Γ k}{B : Ty Γ l} → Tm Γ A → Tm (Γ ▶ B) (A [ wk {l} ]T)
vs {P}{l} t = vsP {l} t
vs {S}{l} t = vsS {l} t

-- It's kind of amazing that this works
<_>S : ∀{Γ}{A : TyS Γ} → TmS Γ A → Sub Γ (Γ ▶S A)
< t >S = id ,sS t
infix 4 <_>S

<_>P : ∀{Γ}{A : TyP Γ} → TmP Γ A → Sub Γ (Γ ▶P A)
< t >P = record
           { ᴬ   = λ γᴬ → γᴬ , t.ᴬ γᴬ ;
             ᴹ   = λ γᴹ → γᴹ , t.ᴹ γᴹ ;
             sz  = S.< t.sz > ;
             Cod = λ γ → refl ;
             Dec = λ γ α → refl }
  where
    module t = TmP t
infix 4 <_>P

<_> : ∀{k Γ}{A : Ty Γ k} → Tm Γ A → Sub Γ (Γ ▶ A)
<_> {P} = <_>P
<_> {S} = <_>S
infix 4 <_>

atS : ∀{Γ a}{B : TyS (Γ ▶P El a)}(t : TmS Γ (ΠS a B))(u : TmP Γ (El a)) → TmS Γ (B [ < u >P ]TS)
atS {Γ}{a}{B} t u = appS {Γ}{a}{B} t [ < u >P ]tS

atP : ∀{Γ a}{B : TyP (Γ ▶P El a)}(t : TmP Γ (ΠP a B))(u : TmP Γ (El a)) → TmP Γ (B [ < u >P ]TP)
atP {Γ}{a}{B} t u = appP {Γ}{a}{B} t [ < u >P ]tP

_^P_ : ∀{Γ Δ : Con}(σ : Sub Γ Δ)(A : TyP Δ) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^P_ {Γ} {Δ} σ A = σ ∘ (wk {A = A [ σ ]T}) ,sP (vz {Γ = Γ}{A [ σ ]T})

_^S_ : ∀{Γ Δ : Con}(σ : Sub Γ Δ)(B : TyS Δ) → Sub (Γ ▶ (B [ σ ]T)) (Δ ▶ B)
_^S_ {Γ} {Δ} σ B = σ ∘ (wk {A = B [ σ ]T}) ,sS (vz {Γ = Γ}{B [ σ ]T})

_^_ : ∀{k}{Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {P} = _^P_
_^_ {S} = _^S_

infixl 5 _^_

