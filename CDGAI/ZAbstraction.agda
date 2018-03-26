module CDGAI.ZAbstraction where

open import Prelude
open import Poset
open import CDGAI.ASyntax
open import CDGAI.ASemantics
open import CDGAI.BoolAbstraction

postulate
  ℤ♯ : Poset 0ᴸ
  ⇄ℤ⇄ : ⇧ ℤ ⇄ᶜ ℤ♯
  ⊤ℤ♯ : ⟪ ℤ♯ ⟫
  η[⊤ℤ] : (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) *♮ ⋅ all♮ (⇧ ℤ) ⊑♮ return♮ ⋅ ⊤ℤ♯
  ⟦_⟧ᵃ¹♯ : unary → ⟪ ℤ♯ ↗ ℤ♯ ⟫
  α[⟦⟧ᵃ¹] : ∀ {o} → α[ ⇄ℤ⇄ ↗⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ (pure ⋅ ⟦ o ⟧ᵃ¹♮) ⊑♮ pure ⋅ ⟦ o ⟧ᵃ¹♯
  ⟦_⟧ᵃ²♯ : binary → ⟪ ℤ♯ ↗ ℤ♯ ↗ ℤ♯ ⟫
  α[⟦⟧ᵃ²] : ∀ {o} → α[ (⇄ℤ⇄ ∧⸢⇄ᶜ⸣ ⇄ℤ⇄) ↗⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ (uncurry♮ ⋅ ⟦ o ⟧ᵃ²♮) ⊑♮ pure ⋅ (uncurry♮ ⋅ ⟦ o ⟧ᵃ²♯)
  [⁇ᴮ[≡]♯] : ⟪ ℤ♯ ↗ ℤ♯ ↗ ⇧ 𝔹♯ ⟫
  [⁇ᴮ[<]♯] : ⟪ ℤ♯ ↗ ℤ♯ ↗ ⇧ 𝔹♯ ⟫
