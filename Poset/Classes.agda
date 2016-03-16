module Poset.Classes where

open import Prelude
open import Poset.Poset
open import Poset.Fun
open import Poset.Power

record Logical[↗]
  {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ ℓ₁₂ʳ} {A : Poset ℓ₁} {B : Poset ℓ₂}
  (_R₁_ : relation ℓ₁ʳ ⟪ A ⟫) {{R₁-Refl : Reflexive _R₁_}} {{R₁-Trans : Transitive _R₁_}}
  (_R₂_ : relation ℓ₂ʳ ⟪ B ⟫) {{R₂-Refl : Reflexive _R₂_}} {{R₂-Trans : Transitive _R₂_}}
  (_R₁₂_ : relation ℓ₁₂ʳ ⟪ A ↗ B ⟫) {{R₁₂-Refl : Reflexive _R₁₂_}} {{R₁₂-Trans : Transitive _R₁₂_}}
  : Set (ℓ₁ ⊔ᴸ ℓ₁ʳ ⊔ᴸ ℓ₂ ⊔ᴸ ℓ₂ʳ ⊔ᴸ ℓ₁₂ʳ) where
  field
    res[fx][↗] : ∀ {f g : ⟪ A ↗ B ⟫} {x y : ⟪ A ⟫} → f R₁₂ g → x R₁ y → (f ⋅ x) R₂ (g ⋅ y)
  res[•x][↗] : ∀ {f : ⟪ A ↗ B ⟫} {x y : ⟪ A ⟫} → x R₁ y → (f ⋅ x) R₂ (f ⋅ y)
  res[•x][↗] {f} = res[fx][↗] (xRx {x = f})
  res[f•][↗] : ∀ {f g : ⟪ A ↗ B ⟫} {x : ⟪ A ⟫} → f R₁₂ g → (f ⋅ x) R₂ (g ⋅ x)
  res[f•][↗] f₁Rf₂ = res[fx][↗] f₁Rf₂ (xRx {{R₁-Refl}})
open Logical[↗] {{...}} public

instance
  Logical[↗][≡] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → Logical[↗] (_≡_ {A = ⟪ A ⟫}) (_≡_ {A = ⟪ B ⟫}) (_≡_ {A = ⟪ A ↗ B ⟫})
  Logical[↗][≡] = record { res[fx][↗] = res[•xy] }
  Logical[↗][⊑] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → Logical[↗] (_⊑♮_ {A = A}) (_⊑♮_ {A = B}) (_⊑♮_ {A = A ↗ B})
  Logical[↗][⊑] = record { res[fx][↗] = res[fx]⸢⊑↗⸣ }
  Logical[↗][≈] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → Logical[↗] (_≈♮_ {A = A}) (_≈♮_ {A = B}) (_≈♮_ {A = A ↗ B})
  Logical[↗][≈] = record { res[fx][↗] = res[fx]⸢≈↗⸣ }

record Extensional[↗]
  {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ ℓ₁₂ʳ} {A : Poset ℓ₁} {B : Poset ℓ₂}
  (_R₁_ : relation ℓ₁ʳ ⟪ A ⟫) {{R₁-Refl : Reflexive _R₁_}} {{R₁-Trans : Transitive _R₁_}}
  (_R₂_ : relation ℓ₂ʳ ⟪ B ⟫) {{R₂-Refl : Reflexive _R₂_}} {{R₂-Trans : Transitive _R₂_}}
  (_R₁₂_ : relation ℓ₁₂ʳ ⟪ A ↗ B ⟫) {{R₁₂-Refl : Reflexive _R₁₂_}} {{R₁₂-Trans : Transitive _R₁₂_}}
  : Set (ℓ₁ ⊔ᴸ ℓ₁ʳ ⊔ᴸ ℓ₂ ⊔ᴸ ℓ₂ʳ ⊔ᴸ ℓ₁₂ʳ) where
  field
    ext[↗] : ∀ {f g : ⟪ A ↗ B ⟫} → (∀ {x : ⟪ A ⟫} → (f ⋅ x) R₂ (g ⋅ x)) → f R₁₂ g
open Extensional[↗] {{...}} public

instance
  Extensional[↗][⊑] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → Extensional[↗] (_⊑♮_ {A = A}) (_⊑♮_ {A = B}) (_⊑♮_ {A = A ↗ B})
  Extensional[↗][⊑] = record { ext[↗] = ext⸢⊑↗⸣ }
  Extensional[↗][≈] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → Extensional[↗] (_≈♮_ {A = A}) (_≈♮_ {A = B}) (_≈♮_ {A = A ↗ B})
  Extensional[↗][≈] = record { ext[↗] = ext⸢≈↗⸣ }
