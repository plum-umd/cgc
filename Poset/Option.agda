module Poset.Option where

open import Prelude
open import Poset.Poset
open import Poset.Fun

infix 14 _≼⸢option⸣_
infixr 30 _⊚⸢≼⸢option⸣⸣_

data option♭ {ℓ} (A : Poset ℓ) : Set ℓ where
  None : option♭ A
  Some : ⟪ A ⟫ → option♭ A

data _≼⸢option⸣_ {ℓ} {A : Poset ℓ} : relation ℓ (option♭ A) where
  None : ∀ {xM} → None ≼⸢option⸣ xM
  Some : ∀ {x y} → x ⊑♮ y → Some x ≼⸢option⸣ Some y

xRx⸢≼⸢option⸣⸣ : ∀ {ℓ} {A : Poset ℓ} → reflexive (_≼⸢option⸣_ {A = A})
xRx⸢≼⸢option⸣⸣ {x = None} = None
xRx⸢≼⸢option⸣⸣ {x = Some x} = Some xRx

_⊚⸢≼⸢option⸣⸣_ : ∀ {ℓ} {A : Poset ℓ} → transitive (_≼⸢option⸣_ {A = A})
y⊑z ⊚⸢≼⸢option⸣⸣ None = None
Some y⊑z ⊚⸢≼⸢option⸣⸣ Some x⊑y = Some (y⊑z ⊚ x⊑y)

instance
  Reflexive[≼⸢option⸣] : ∀ {ℓ} {A : Poset ℓ} → Reflexive (_≼⸢option⸣_ {A = A})
  Reflexive[≼⸢option⸣] = record { xRx = xRx⸢≼⸢option⸣⸣ }
  Transitive[≼⸢option⸣] : ∀ {ℓ} {A : Poset ℓ} → Transitive (_≼⸢option⸣_ {A = A})
  Transitive[≼⸢option⸣] = record { _⊚_ = _⊚⸢≼⸢option⸣⸣_ }
  PreOrder[option] : ∀ {ℓ} {A : Poset ℓ} → PreOrder (ℓ) (option♭ A)
  PreOrder[option] = record { _≼_ = _≼⸢option⸣_ }

option♮ : ∀ {ℓ} → Poset ℓ → Poset ℓ
option♮ A = ⇧ (option♭ A)

-- ♮⸢option⸣ : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} → option A → ⟪ option♮ (⇧ A) ⟫
-- ♮⸢option⸣ = {!!}
