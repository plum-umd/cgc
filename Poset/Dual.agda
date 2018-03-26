module Poset.Dual where

open import Prelude
open import Poset.Poset

infixr 14 _≼⸢dual⸣_
infixr 30 _⊚⸢≼⸢dual⸣⸣_

data dual {ℓ} (A : Poset ℓ) : Set ℓ where
  ♮⟨_⟩ : ⟪ A ⟫ → dual A

data _≼⸢dual⸣_ {ℓ} {A : Poset ℓ} : relation ℓ (dual A) where
  ♮⟨_⟩ : ∀ {x y} → y ⊑♮ x → ♮⟨ x ⟩ ≼⸢dual⸣ ♮⟨ y ⟩

xRx⸢≼⸢dual⸣⸣ : ∀ {ℓ} {A : Poset ℓ} → reflexive (_≼⸢dual⸣_ {A = A})
xRx⸢≼⸢dual⸣⸣ {x = ♮⟨ x ⟩} = ♮⟨ xRx ⟩

_⊚⸢≼⸢dual⸣⸣_ : ∀ {ℓ} {A : Poset ℓ} → transitive (_≼⸢dual⸣_ {A = A})
♮⟨ z⊑y ⟩ ⊚⸢≼⸢dual⸣⸣ ♮⟨ y⊑x ⟩ = ♮⟨ y⊑x ⊚ z⊑y ⟩

instance
  Reflexive[dual] : ∀ {ℓ} {A : Poset ℓ} → Reflexive (_≼⸢dual⸣_ {A = A})
  Reflexive[dual] = record { xRx = xRx⸢≼⸢dual⸣⸣ }
  Transitive[dual] : ∀ {ℓ} {A : Poset ℓ} → Transitive (_≼⸢dual⸣_ {A = A})
  Transitive[dual] = record { _⊚_ = _⊚⸢≼⸢dual⸣⸣_ }
  Precision[dual] : ∀ {ℓ} {A : Poset ℓ} → Precision ℓ (dual A)
  Precision[dual] = mk[Precision] _≼⸢dual⸣_
