module Prelude.Data.Option where

open import Prelude.Core

mapᵒ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → option A → option B
mapᵒ f None = None
mapᵒ f (Some x) = Some (f x)
