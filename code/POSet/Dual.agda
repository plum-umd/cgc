module POSet.Dual where

open import Prelude
open import POSet.POSet

data dual {𝓁} (A : POSet 𝓁) : Set 𝓁 where
  ↑⟨_⟩ : ⟪ A ⟫ → dual A

infixr 8 _⊴⸢dual⸣_
data _⊴⸢dual⸣_ {𝓁} {A : POSet 𝓁} : relation 𝓁 (dual A) where
  ↑⟨_⟩ : ∀ {x y} → y ⊑ x → ↑⟨ x ⟩ ⊴⸢dual⸣ ↑⟨ y ⟩

xRx⸢⊴⸢dual⸣⸣ : ∀ {𝓁} {A : POSet 𝓁} → reflexive (_⊴⸢dual⸣_ {A = A})
xRx⸢⊴⸢dual⸣⸣ {x = ↑⟨ x ⟩} = ↑⟨ xRx ⟩

infixr 9 _⌾⸢⊴⸢dual⸣⸣_
_⌾⸢⊴⸢dual⸣⸣_ : ∀ {𝓁} {A : POSet 𝓁} → transitive (_⊴⸢dual⸣_ {A = A})
↑⟨ z⊑y ⟩ ⌾⸢⊴⸢dual⸣⸣ ↑⟨ y⊑x ⟩ = ↑⟨ y⊑x ⌾ z⊑y ⟩

instance
  Reflexive[dual] : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_⊴⸢dual⸣_ {A = A})
  Reflexive[dual] = record { xRx = xRx⸢⊴⸢dual⸣⸣ }
  Transitive[dual] : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_⊴⸢dual⸣_ {A = A})
  Transitive[dual] = record { _⌾_ = _⌾⸢⊴⸢dual⸣⸣_ }
  PreOrder[dual] : ∀ {𝓁} {A : POSet 𝓁} → PreOrder 𝓁 (dual A)
  PreOrder[dual] = record { _⊴_ = _⊴⸢dual⸣_ }
