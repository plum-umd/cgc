module Data.Option where

open import Core

map⸢option⸣ : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} → (A → B) → option A → option B
map⸢option⸣ f None = None
map⸢option⸣ f (Some x) = Some (f x)
