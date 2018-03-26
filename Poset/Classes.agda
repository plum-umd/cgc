module Poset.Classes where

open import Prelude
open import Poset.Poset
open import Poset.Fun
open import Poset.Power

module Logical[↗]
  (_R_ : ∀ {ℓ} {A : Poset ℓ} → relation ℓ ⟪ A ⟫)
  {{_ : ∀ {ℓ} {A : Poset ℓ} → Reflexive (_R_ {ℓ} {A})}}
  (res[fx][↗] :
     ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} {f g : ⟪ A ↗ B ⟫} {x y : ⟪ A ⟫}
     → f R g → x R y → (f ⋅ x) R (g ⋅ y))
  where
    res[•x][↗] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} {f : ⟪ A ↗ B ⟫} {x y : ⟪ A ⟫} → x R y → (f ⋅ x) R (f ⋅ y)
    res[•x][↗] {f = f} = res[fx][↗] (xRx {x = f})
    res[f•][↗] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} {f g : ⟪ A ↗ B ⟫} {x : ⟪ A ⟫} → f R g → (f ⋅ x) R (g ⋅ x)
    res[f•][↗] f₁Rf₂ = res[fx][↗] f₁Rf₂ xRx

module Logical[↗]⸢≡⸣ = Logical[↗] _≡_ res[•xy]
open Logical[↗]⸢≡⸣ public
  using ()
  renaming
  ( res[•x][↗] to res[•x][↗]⸢≡⸣
  ; res[f•][↗] to res[f•][↗]⸢≡⸣
  )

module Logical[↗]⸢⊑⸣ = Logical[↗] _⊑♮_ res[fx][↗]⸢⊑⸣
open Logical[↗]⸢⊑⸣ public
  using ()
  renaming
  ( res[•x][↗] to res[•x][↗]⸢⊑⸣
  ; res[f•][↗] to res[f•][↗]⸢⊑⸣
  )

module Logical[↗]⸢≈⸣ = Logical[↗] _≈♮_ res[fx][↗]⸢≈⸣
open Logical[↗]⸢≈⸣ public
  using ()
  renaming
  ( res[•x][↗] to res[•x][↗]⸢≈⸣
  ; res[f•][↗] to res[f•][↗]⸢≈⸣
  )
