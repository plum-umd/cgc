module POSet.Option where

open import Prelude
open import POSet.POSet
open import POSet.Fun

data option↓ {𝓁} (A : POSet 𝓁) : Set 𝓁 where
  None : option↓ A
  Some : ⟪ A ⟫ → option↓ A

infix 8 _⊴⸢option⸣_
data _⊴⸢option⸣_ {𝓁} {A : POSet 𝓁} : relation 𝓁 (option↓ A) where
  None : ∀ {xM} → None ⊴⸢option⸣ xM
  Some : ∀ {x y} → x ⊑ y → Some x ⊴⸢option⸣ Some y

xRx⸢⊴⸢option⸣⸣ : ∀ {𝓁} {A : POSet 𝓁} → reflexive (_⊴⸢option⸣_ {A = A})
xRx⸢⊴⸢option⸣⸣ {x = None} = None
xRx⸢⊴⸢option⸣⸣ {x = Some x} = Some xRx

infixr 9 _⌾⸢⊴⸢option⸣⸣_
_⌾⸢⊴⸢option⸣⸣_ : ∀ {𝓁} {A : POSet 𝓁} → transitive (_⊴⸢option⸣_ {A = A})
y⊑z ⌾⸢⊴⸢option⸣⸣ None = None
Some y⊑z ⌾⸢⊴⸢option⸣⸣ Some x⊑y = Some (y⊑z ⌾ x⊑y)

instance
  Reflexive[⊴⸢option⸣] : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_⊴⸢option⸣_ {A = A})
  Reflexive[⊴⸢option⸣] = record { xRx = xRx⸢⊴⸢option⸣⸣ }
  Transitive[⊴⸢option⸣] : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_⊴⸢option⸣_ {A = A})
  Transitive[⊴⸢option⸣] = record { _⌾_ = _⌾⸢⊴⸢option⸣⸣_ }
  PreOrder[option] : ∀ {𝓁} {A : POSet 𝓁} → PreOrder (𝓁) (option↓ A)
  PreOrder[option] = record { _⊴_ = _⊴⸢option⸣_ }

option⁺ : ∀ {𝓁} → POSet 𝓁 → POSet 𝓁
option⁺ A = ⇧ (option↓ A)

-- ↑⸢option⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} → option A → ⟪ option⁺ (⇧ A) ⟫
-- ↑⸢option⸣ = {!!}
