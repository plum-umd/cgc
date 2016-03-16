module Prelude.Data.Vector where

open import Prelude.Core
open import Prelude.Data.Natural

infixr 40 _∷_

data vec {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  [] : vec A Zero
  _∷_ : ∀ {n} → A → vec A n → vec A (Succ n)

𝕍 : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ
𝕍 n A = vec A n

_[_]ᵛ : ∀ {ℓ} {A : Set ℓ} {n} → 𝕍 n A → fin n → A
(x ∷ xs) [ Zero ]ᵛ = x
(x ∷ xs) [ Succ n ]ᵛ = xs [ n ]ᵛ
