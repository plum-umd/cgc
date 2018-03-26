module Prelude.Data.Option where

open import Prelude.Core
open import Prelude.Classes
open import Prelude.Orders

mapᵒ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → option A → option B
mapᵒ f None = None
mapᵒ f (Some x) = Some (f x)

module _ {ℓ ℓʳ} {A : Set ℓ} {{_ : Precision ℓʳ A}} where
  data _⊑ᵒ_ : relation ℓʳ (option A) where
    None : None ⊑ᵒ None
    Some : ∀ {x y} → x ⊑ y → Some x ⊑ᵒ Some y

  xRx[⊑]ᵒ : reflexive _⊑ᵒ_
  xRx[⊑]ᵒ {None} = None
  xRx[⊑]ᵒ {Some x} = Some xRx[⊑][ A ]

  _⊚[⊑]ᵒ_ : transitive _⊑ᵒ_
  None ⊚[⊑]ᵒ None = None
  Some y⊑z ⊚[⊑]ᵒ Some x⊑y = Some (y⊑z ⊚[⊑][ A ] x⊑y)

  instance
    Reflexive[⊑]ᵒ : Reflexive _⊑ᵒ_
    Reflexive[⊑]ᵒ = record { xRx = xRx[⊑]ᵒ }
    Transitive[⊑]ᵒ : Transitive _⊑ᵒ_
    Transitive[⊑]ᵒ = record { _⊚_ = _⊚[⊑]ᵒ_ }
    Precision[option] : Precision ℓʳ (option A)
    Precision[option] = mk[Precision] _⊑ᵒ_
