module POSet.Prp where

open import Prelude
open import POSet.POSet

data prop 𝓁 : Set (sucˡ 𝓁) where
  ↑⟨_⟩ : Set 𝓁 → prop 𝓁

infixr 8 _⊴⸢prop⸣_
data _⊴⸢prop⸣_  {𝓁} : relation (sucˡ 𝓁) (prop 𝓁) where
  ↑⟨_⟩ : ∀ {φ₁ φ₂} → (φ₁ → φ₂) → ↑⟨ φ₁ ⟩ ⊴⸢prop⸣ ↑⟨ φ₂ ⟩

xRx⸢⊴⸢prop⸣⸣ : ∀ {𝓁} → reflexive (_⊴⸢prop⸣_ {𝓁})
xRx⸢⊴⸢prop⸣⸣ {x = ↑⟨ φ ⟩} = ↑⟨ id ⟩ 

infixr 9 _⌾⸢⊴⸢prop⸣⸣_
_⌾⸢⊴⸢prop⸣⸣_ : ∀ {𝓁} → transitive (_⊴⸢prop⸣_ {𝓁})
↑⟨ φ₂→φ₃ ⟩ ⌾⸢⊴⸢prop⸣⸣ ↑⟨ φ₁→φ₂ ⟩ = ↑⟨ φ₂→φ₃ ∘ φ₁→φ₂ ⟩

instance
  Reflexive[prop] : ∀ {𝓁} → Reflexive (_⊴⸢prop⸣_ {𝓁})
  Reflexive[prop] = record { xRx = xRx⸢⊴⸢prop⸣⸣ }
  Transitive[prop] : ∀ {𝓁} → Transitive (_⊴⸢prop⸣_ {𝓁})
  Transitive[prop] = record { _⌾_ = _⌾⸢⊴⸢prop⸣⸣_ }
  PreOrder[prop] : ∀ {𝓁} → PreOrder (sucˡ 𝓁) (prop 𝓁)
  PreOrder[prop] = record { _⊴_ = _⊴⸢prop⸣_ }
