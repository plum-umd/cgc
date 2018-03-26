module Prelude.Data.AFMap where

open import Prelude.Core
open import Prelude.Classes
open import Prelude.Orders

postulate
  𝓅 : ∀ {ℓ} (A : Set ℓ) → Set ℓ
  _∈?_ : ∀ {ℓ} {A : Set ℓ} → A → 𝓅 A → ‼
  _∈?_
  _∈_ : ∀ {ℓ ℓʳ} {A : Set ℓ} {{_ : Order ℓʳ A}} → A → 𝓅 A → Set
  _∉_ : ∀ {ℓ ℓʳ} {A : Set ℓ} {{_ : Order ℓʳ A}} → A → 𝓅 A → Set

  _⇰_ : ∀ {ℓ₁ ℓ₁ʳ ℓ₂} (A : Set ℓ₁) {{_ : Order ℓ₁ʳ A}} → Set ℓ₂ → Set (ℓ₁ ⊔ᴸ ℓ₁ʳ ⊔ᴸ ℓ₂)
    
