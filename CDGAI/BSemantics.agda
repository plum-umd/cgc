module CDGAI.BSemantics where

open import Prelude
open import Poset
open import CDGAI.BSyntax
open import CDGAI.ASyntax
open import CDGAI.ASemantics

⟦_⟧ᵇᶜ : comparison → ℤ → ℤ → 𝔹
⟦ [≟] ⟧ᵇᶜ = _⁇ᴮ[≡]_
⟦ [⩻] ⟧ᵇᶜ = _⁇ᴮ[<]_

⟦_⟧ᵇˡ : logical → 𝔹 → 𝔹 → 𝔹
⟦ [∨] ⟧ᵇˡ = _⨹_
⟦ [∧] ⟧ᵇˡ = _⨻_

module _ {Γ} where
  data _⊢_⇓ᵇ_ : env Γ → bexp Γ → 𝔹 → Set where
    True : ∀ {ρ}
      → ρ ⊢ True ⇓ᵇ True
    False : ∀ {ρ}
      → ρ ⊢ False ⇓ᵇ False
    Compare : ∀ {ρ o e₁ e₂ i₁ i₂}
      → ρ ⊢ e₁ ⇓ᵃ i₁
      → ρ ⊢ e₂ ⇓ᵃ i₂
      → ρ ⊢ Compare[ o ] e₁ e₂ ⇓ᵇ ⟦ o ⟧ᵇᶜ i₁ i₂
    Logical : ∀ {ρ l e₁ e₂ b₁ b₂}
      → ρ ⊢ e₁ ⇓ᵇ b₁
      → ρ ⊢ e₂ ⇓ᵇ b₂
      → ρ ⊢ Logical[ l ] e₁ e₂ ⇓ᵇ ⟦ l ⟧ᵇˡ b₁ b₂
  
  ⟦_⟧ᵇ : bexp Γ → ⟪ ⇧ (env Γ) ↗ ℘ (⇧ 𝔹) ⟫
  ⟦ be ⟧ᵇ = witness (curry⸢λ♭⸣ id⸢ω♭⸣) $ mk[witness] (λ ρ b → ρ ⊢ be ⇓ᵇ b) (λ { {x} ↯ ↯ → id })
