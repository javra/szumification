module AMSzIds where

open import Lib hiding (id; _∘_)
open import II using (PS; P; S)
import IIA as S
open import AMSz

[id]T : ∀{k Γ}{A : Ty Γ k} → (A [ id ]T) ≡ A
[id]T {P} = refl
[id]T {S} = refl

[][]T : ∀{k Γ Δ Σ}{A : Ty Σ k}{σ : Sub Γ Δ}{δ : Sub Δ Σ}
          → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T
[][]T {P} = refl
[][]T {S} = refl

idl   : ∀{Γ Δ}{σ : Sub Γ Δ} → (id ∘ σ) ≡ σ
idl = refl

idr   : ∀{Γ Δ}{σ : Sub Γ Δ} → (σ ∘ id) ≡ σ
idr = refl

ass   : ∀{Γ Δ Σ Ω}{σ : Sub Σ Ω}{δ : Sub Δ Σ}{ν : Sub Γ Δ}
        → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
ass = refl

,∘    : ∀{k Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub Σ Γ}{A : Ty Δ k}{t : Tm Γ (A [ δ ]T)}
        → ((δ ,s t) ∘ σ) ≡ ((δ ∘ σ) ,s tr (Tm Σ) [][]T (t [ σ ]t))
,∘ {P} = refl
,∘ {S} = refl

π₁β   : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
        → (π₁ {k} (σ ,s t)) ≡ σ
π₁β {P} = refl
π₁β {S} = refl

πη    : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ (Δ ▶ A)}
        → (π₁ {k} σ ,s π₂ {k} σ) ≡ σ
πη {P} = refl
πη {S} = refl

εη    : ∀{Γ}{σ : Sub Γ ∙} → σ ≡ ε
εη = {!!}

π₂β   : ∀{k Γ Δ}{A : Ty Δ k}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
        → π₂ (σ ,s t) ≡ tr (λ σ → Tm Γ (A [ σ ]T)) (π₁β {k} ⁻¹) t
π₂β {P} = refl
π₂β {S} = refl

U[]  : ∀{Γ Δ}{σ : Sub Γ Δ} → (U [ σ ]T) ≡ U
U[] = {!!}

El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}
       → (El a [ σ ]T) ≡ (El (coe (Tm Γ & (U[] {Γ}{Δ}{σ})) (a [ σ ]t)))
El[] = {!!}

Π[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a) k}
      → (Π a B) [ σ ]T ≡ Π (tr (Tm Γ) U[] (a [ σ ]t))
                           (tr (λ x → Ty (Γ ▶ x) k) El[] (B [ σ ^ El a ]T))
Π[] {P} = {!!}
Π[] {S} = {!!}

app[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a) k}{t : Tm Δ (Π a B)}
          → tr2 (λ A → Tm (Γ ▶ A)) El[] refl (app t [ σ ^ El a ]t)
          ≡ app (tr (Tm _) Π[] (t [ σ ]t))
app[] = {!!}

Π̂[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{T : Set}{B : T → Ty Δ k}
        → (Π̂ T B) [ σ ]T ≡ Π̂ T λ τ → B τ [ σ ]T
Π̂[] {P} = refl
Π̂[] {S} = refl

âpp[] : ∀{k Γ Δ}{σ : Sub Γ Δ}{T}{B : T → Ty Δ k}{f : Tm Δ (Π̂ T B)}{τ : T}
          → âpp {B = λ τ → B τ [ σ ]T} (tr (Tm Γ) Π̂[] (f [ σ ]t)) τ ≡ (âpp f τ) [ σ ]t
âpp[] {P} = refl
âpp[] {S} = refl
