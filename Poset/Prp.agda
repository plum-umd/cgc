module Poset.Prp where

open import Prelude
open import Poset.Poset

infixr 14 _≼⸢prop⸣_
infixr 30 _⊚⸢≼⸢prop⸣⸣_

data prop ℓ : Set (↑ᴸ ℓ) where
  ♮⟨_⟩ : Set ℓ → prop ℓ

data _≼⸢prop⸣_  {ℓ} : relation (↑ᴸ ℓ) (prop ℓ) where
  ♮⟨_⟩ : ∀ {φ₁ φ₂} → (φ₁ → φ₂) → ♮⟨ φ₁ ⟩ ≼⸢prop⸣ ♮⟨ φ₂ ⟩

xRx⸢≼⸢prop⸣⸣ : ∀ {ℓ} → reflexive (_≼⸢prop⸣_ {ℓ})
xRx⸢≼⸢prop⸣⸣ {x = ♮⟨ φ ⟩} = ♮⟨ id ⟩ 

_⊚⸢≼⸢prop⸣⸣_ : ∀ {ℓ} → transitive (_≼⸢prop⸣_ {ℓ})
♮⟨ φ₂→φ₃ ⟩ ⊚⸢≼⸢prop⸣⸣ ♮⟨ φ₁→φ₂ ⟩ = ♮⟨ φ₂→φ₃ ∘ φ₁→φ₂ ⟩

instance
  Reflexive[prop] : ∀ {ℓ} → Reflexive (_≼⸢prop⸣_ {ℓ})
  Reflexive[prop] = record { xRx = xRx⸢≼⸢prop⸣⸣ }
  Transitive[prop] : ∀ {ℓ} → Transitive (_≼⸢prop⸣_ {ℓ})
  Transitive[prop] = record { _⊚_ = _⊚⸢≼⸢prop⸣⸣_ }
  PreOrder[prop] : ∀ {ℓ} → PreOrder (↑ᴸ ℓ) (prop ℓ)
  PreOrder[prop] = record { _≼_ = _≼⸢prop⸣_ }
