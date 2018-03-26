module Poset where

open import Prelude

open import Poset.Classes public
open import Poset.Dual public
open import Poset.Fun public
open import Poset.GaloisConnection public
open import Poset.Lib public
open import Poset.Poset public
open import Poset.Power public
open import Poset.PowerMonad public
open import Poset.Product public
open import Poset.List public
open import Poset.Option public
-- open import Poset.Option public
open import Poset.ProofMode public
-- open import Poset.Prp public

instance
  PreOrder[ℕ] : Precision 0ᴸ ℕ
  PreOrder[ℕ] = mk[Precision] _≡_
  PreOrder[ℤ] : Precision 0ᴸ ℤ
  PreOrder[ℤ] = mk[Precision] _≡_
  PreOrder[𝔹] : Precision 0ᴸ 𝔹
  PreOrder[𝔹] = mk[Precision] _≡_

-- option⸢⇄ᶜ⸣[_] : ∀ {ℓ} {A₁ A₂ : Poset ℓ} → A₁ ⇄ᶜ A₂ → option♮ A₁ ⇄ᶜ option♮ A₂
-- option⸢⇄ᶜ⸣[_] {ℓ} {A₁} {A₂} ⇄A⇄ = mk[⇄ᶜ♭] record
--   { η = η
--   ; monotonic[η] = monotonic[η]
--   ; γ = λ x y → y ∈γ⸢option⸣[ x ]
--   ; monotonic[γ] = monotonic[γ]
--   ; sound = λ {x} → sound {x}
--   ; complete = λ {x} {x♯} → complete {x} {x♯}
--   }
--   where
--     η : option♭ A₁ → option♭ A₂
--     η None = None
--     η (Some x) = Some (ηᶜ[ ⇄A⇄ ] ⋅ x)
--     monotonic[η] : ∀ {x y : option♭ A₁} → x ≼⸢option⸣ y → η x ≼⸢option⸣ η y
--     monotonic[η] None = None
--     monotonic[η] (Some x⊑y) = Some (res[x]⸢⊑↗⸣ {f = ηᶜ[ ⇄A⇄ ]} x⊑y)
--     data _∈γ⸢option⸣[_] : option♭ A₁ → option♭ A₂ → Set ℓ where
--       None : ∀ {xM} → None ∈γ⸢option⸣[ xM ]
--       Some : ∀ {x x♯} → x ⋿ γᶜ[ ⇄A⇄ ] ⋅ x♯ → Some x ∈γ⸢option⸣[ Some x♯ ]
--     monotonic[γ] : ∀ {x₁ x₂ : option♭ A₂} → x₁ ≼⸢option⸣ x₂ → ∀ {y₁ y₂ : option♭ A₁} → y₂ ≼⸢option⸣ y₁ → y₁ ∈γ⸢option⸣[ x₁ ] → y₂ ∈γ⸢option⸣[ x₂ ]
--     monotonic[γ] x₁⊴x₂ None None∈γ[x₁] = None
--     monotonic[γ] (Some x₁⊴x₂) (Some y₂⊴y₁) (Some y₁∈γ[x₁]) = Some (res[Xx]⸢⊑𝒫⸣ (res[x]⸢⊑↗⸣ {f = γᶜ[ ⇄A⇄ ]} x₁⊴x₂) y₂⊴y₁ y₁∈γ[x₁])
--     sound : ∀ {x : option♭ A₁} → x ∈γ⸢option⸣[ η x ]
--     sound {None} = None
--     sound {Some x} = Some soundᶜ[ ⇄A⇄ ]
--     complete : ∀ {x : option♭ A₁} {x♯ : option♭ A₂} → x ∈γ⸢option⸣[ x♯ ] → η x ≼⸢option⸣ x♯
--     complete None = None
--     complete (Some x∈γᶜ[x♯]) = Some (completeᶜ[ ⇄A⇄ ] x∈γᶜ[x♯])
