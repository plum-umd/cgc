module CDGAI.BSemantics where

open import Prelude
open import POSet
open import CDGAI.BSyntax
open import CDGAI.ASemantics

-- stuff that should probably go into standard lib

_≟ᴺ_ : ℕ → ℕ → 𝔹
Zero ≟ᴺ Zero = True
Zero ≟ᴺ Suc n₂ = False
Suc n₁ ≟ᴺ Zero = False
Suc n₁ ≟ᴺ Suc n₂ = n₁ ≟ᴺ n₂

_≟ᶻ_ : ℤ → ℤ → 𝔹
Pos n₁ ≟ᶻ Pos n₂ = n₁ ≟ᴺ n₂
Pos n₁ ≟ᶻ Zero = False
Pos n₁ ≟ᶻ Neg n₂ = False
Zero ≟ᶻ Pos n₂ = False
Zero ≟ᶻ Zero = True
Zero ≟ᶻ Neg n₂ = False
Neg n₁ ≟ᶻ Pos n₂ = False
Neg n₁ ≟ᶻ Zero = False
Neg n₁ ≟ᶻ Neg n₂ = n₁ ≟ᴺ n₂

_⩻ᴺ_ : ℕ → ℕ → 𝔹
Zero ⩻ᴺ Zero = False
Zero ⩻ᴺ Suc n₂ = True
Suc n₁ ⩻ᴺ Zero = False
Suc n₁ ⩻ᴺ Suc n₂ = n₁ ⩻ᴺ n₂

_⩻ᶻ_ : ℤ → ℤ → 𝔹
Pos n₁ ⩻ᶻ Pos n₂ = n₁ ⩻ᴺ n₂
Pos n₁ ⩻ᶻ Zero = False
Pos n₁ ⩻ᶻ Neg n₂ = False
Zero ⩻ᶻ Pos n₂ = True
Zero ⩻ᶻ Zero = False
Zero ⩻ᶻ Neg n₂ = False
Neg n₁ ⩻ᶻ Pos n₂ = True
Neg n₁ ⩻ᶻ Zero = True
Neg n₁ ⩻ᶻ Neg n₂ = n₂ ⩻ᴺ n₁

⟦_⟧ᵇᶜ : comparison → ℤ → ℤ → 𝔹
⟦ [≟] ⟧ᵇᶜ = _≟ᶻ_
⟦ [⩻] ⟧ᵇᶜ = _⩻ᶻ_

_∨_ : 𝔹 → 𝔹 → 𝔹
True ∨ b₂ = True
b₁ ∨ True = True
False ∨ b₂ = b₂

_∧_ : 𝔹 → 𝔹 → 𝔹
True ∧ b₂ = b₂
b₁ ∧ True = b₁
False ∧ b₂ = False

⟦_⟧ᵇˡ : logical → 𝔹 → 𝔹 → 𝔹
⟦ [∨] ⟧ᵇˡ = _∨_
⟦ [∧] ⟧ᵇˡ = _∧_

data _⊢_⇓ᵇ_ {Γ} : env Γ → bexp Γ → 𝔹 → Set where
  True : ∀ {ρ} → ρ ⊢ True ⇓ᵇ True
  False : ∀ {ρ} → ρ ⊢ False ⇓ᵇ False
  Compare : ∀ {ρ o e₁ e₂ i₁ i₂} → ρ ⊢ e₁ ⇓ᵃ i₁ → ρ ⊢ e₂ ⇓ᵃ i₂ → ρ ⊢ Compare[ o ] e₁ e₂ ⇓ᵇ ⟦ o ⟧ᵇᶜ i₁ i₂
  Logical : ∀ {ρ l e₁ e₂ b₁ b₂} → ρ ⊢ e₁ ⇓ᵇ b₁ → ρ ⊢ e₂ ⇓ᵇ b₂ → ρ ⊢ Logical[ l ] e₁ e₂ ⇓ᵇ ⟦ l ⟧ᵇˡ b₁ b₂

postulate
  ⟦_⟧ᵇ♯ : ∀ {Γ} → bexp Γ → ⟪ ⇧ (env Γ) ⇒ 𝒫 (⇧ 𝔹) ⟫
