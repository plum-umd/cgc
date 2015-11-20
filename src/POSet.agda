module POSet where

open import Prelude

open import POSet.Classes public
open import POSet.Dual public
open import POSet.Fun public
open import POSet.GaloisConnection public
open import POSet.Lib public
open import POSet.POSet public
open import POSet.Power public
open import POSet.PowerMonad public
open import POSet.Product public
open import POSet.Option public
open import POSet.ProofMode public
open import POSet.Prp public

instance
  PreOrder[ℕ] : PreOrder zeroˡ ℕ
  PreOrder[ℕ] = ≡-PreOrder
  PreOrder[ℤ] : PreOrder zeroˡ ℤ
  PreOrder[ℤ] = ≡-PreOrder
  PreOrder[𝔹] : PreOrder zeroˡ 𝔹
  PreOrder[𝔹] = ≡-PreOrder

option⸢⇄ᶜ⸣[_] : ∀ {𝓁} {A₁ A₂ : POSet 𝓁} → A₁ ⇄ᶜ A₂ → option⁺ A₁ ⇄ᶜ option⁺ A₂
option⸢⇄ᶜ⸣[_] {𝓁} {A₁} {A₂} ⇄A⇄ = mk[⇄ᶜ]⸢↑⸣ record
  { η = η
  ; monotonic[η] = monotonic[η]
  ; γ = λ x y → y ∈γ⸢option⸣[ x ]
  ; monotonic[γ] = monotonic[γ]
  ; sound = λ {x} → sound {x}
  ; complete = λ {x} {x♯} → complete {x} {x♯}
  }
  where
    η : option↓ A₁ → option↓ A₂
    η None = None
    η (Some x) = Some (ηᶜ[ ⇄A⇄ ] ⋅ x)
    monotonic[η] : ∀ {x y : option↓ A₁} → x ⊴⸢option⸣ y → η x ⊴⸢option⸣ η y
    monotonic[η] None = None
    monotonic[η] (Some x⊑y) = Some (res-x[⇒]⸢⊑⸣ {f = ηᶜ[ ⇄A⇄ ]} x⊑y)
    data _∈γ⸢option⸣[_] : option↓ A₁ → option↓ A₂ → Set 𝓁 where
      None : ∀ {xM} → None ∈γ⸢option⸣[ xM ]
      Some : ∀ {x x♯} → x ⋿ γᶜ[ ⇄A⇄ ] ⋅ x♯ → Some x ∈γ⸢option⸣[ Some x♯ ]
    monotonic[γ] : ∀ {x₁ x₂ : option↓ A₂} → x₁ ⊴⸢option⸣ x₂ → ∀ {y₁ y₂ : option↓ A₁} → y₂ ⊴⸢option⸣ y₁ → y₁ ∈γ⸢option⸣[ x₁ ] → y₂ ∈γ⸢option⸣[ x₂ ]
    monotonic[γ] x₁⊴x₂ None None∈γ[x₁] = None
    monotonic[γ] (Some x₁⊴x₂) (Some y₂⊴y₁) (Some y₁∈γ[x₁]) = Some (res-X-x[𝒫]⸢⊑⸣ (res-x[⇒]⸢⊑⸣ {f = γᶜ[ ⇄A⇄ ]} x₁⊴x₂) y₂⊴y₁ y₁∈γ[x₁])
    sound : ∀ {x : option↓ A₁} → x ∈γ⸢option⸣[ η x ]
    sound {None} = None
    sound {Some x} = Some soundᶜ[ ⇄A⇄ ]
    complete : ∀ {x : option↓ A₁} {x♯ : option↓ A₂} → x ∈γ⸢option⸣[ x♯ ] → η x ⊴⸢option⸣ x♯
    complete None = None
    complete (Some x∈γᶜ[x♯]) = Some (completeᶜ[ ⇄A⇄ ] x∈γᶜ[x♯])
