module Prelude.Data.Vector where

open import Prelude.Core
open import Prelude.Data.Natural

data vec {𝓁} (A : Set 𝓁) : ℕ → Set 𝓁 where
  [] : vec A Zero
  _∷_ : ∀ {n} → A → vec A n → vec A (Suc n)

𝕍 : ∀ {𝓁} → ℕ → Set 𝓁 → Set 𝓁
𝕍 n A = vec A n

_[_]ᵛ : ∀ {𝓁} {A : Set 𝓁} {n} → 𝕍 n A → fin n → A
(x ∷ xs) [ Zero ]ᵛ = x
(x ∷ xs) [ Suc n ]ᵛ = xs [ n ]ᵛ
