module POSet.Classes where

open import Prelude
open import POSet.POSet
open import POSet.Fun
open import POSet.Power

record Logical[⇒]
  {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ 𝓁₁₂ʳ} {A : POSet 𝓁₁} {B : POSet 𝓁₂}
  (_R₁_ : relation 𝓁₁ʳ ⟪ A ⟫) {{R₁-Refl : Reflexive _R₁_}} {{R₁-Trans : Transitive _R₁_}}
  (_R₂_ : relation 𝓁₂ʳ ⟪ B ⟫) {{R₂-Refl : Reflexive _R₂_}} {{R₂-Trans : Transitive _R₂_}}
  (_R₁₂_ : relation 𝓁₁₂ʳ ⟪ A ⇒ B ⟫) {{R₁₂-Refl : Reflexive _R₁₂_}} {{R₁₂-Trans : Transitive _R₁₂_}}
  : Set (𝓁₁ ⊔ˡ 𝓁₁ʳ ⊔ˡ 𝓁₂ ⊔ˡ 𝓁₂ʳ ⊔ˡ 𝓁₁₂ʳ) where
  field
    res-f-x[⇒] : ∀ {f g : ⟪ A ⇒ B ⟫} {x y : ⟪ A ⟫} → f R₁₂ g → x R₁ y → (f ⋅ x) R₂ (g ⋅ y)
  res-x[⇒] : ∀ {f : ⟪ A ⇒ B ⟫} {x y : ⟪ A ⟫} → x R₁ y → (f ⋅ x) R₂ (f ⋅ y)
  res-x[⇒] {f} = res-f-x[⇒] (xRx {x = f})
  res-f[⇒] : ∀ {f g : ⟪ A ⇒ B ⟫} {x : ⟪ A ⟫} → f R₁₂ g → (f ⋅ x) R₂ (g ⋅ x)
  res-f[⇒] f₁Rf₂ = res-f-x[⇒] f₁Rf₂ xRx
open Logical[⇒] {{...}} public

instance
  Logical[⇒][≡] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical[⇒] (_≡_ {A = ⟪ A ⟫}) (_≡_ {A = ⟪ B ⟫}) (_≡_ {A = ⟪ A ⇒ B ⟫})
  Logical[⇒][≡] = record { res-f-x[⇒] = res2-xy }
  Logical[⇒][⊑] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical[⇒] (_⊑_ {A = A}) (_⊑_ {A = B}) (_⊑_ {A = A ⇒ B})
  Logical[⇒][⊑] = record { res-f-x[⇒] = res-f-x[⇒]⸢⊑⸣ }
  Logical[⇒][≈] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical[⇒] (_≈_ {A = A}) (_≈_ {A = B}) (_≈_ {A = A ⇒ B})
  Logical[⇒][≈] = record { res-f-x[⇒] = res-f-x[⇒]⸢≈⸣ }

record Extensional[⇒]
  {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ 𝓁₁₂ʳ} {A : POSet 𝓁₁} {B : POSet 𝓁₂}
  (_R₁_ : relation 𝓁₁ʳ ⟪ A ⟫) {{R₁-Refl : Reflexive _R₁_}} {{R₁-Trans : Transitive _R₁_}}
  (_R₂_ : relation 𝓁₂ʳ ⟪ B ⟫) {{R₂-Refl : Reflexive _R₂_}} {{R₂-Trans : Transitive _R₂_}}
  (_R₁₂_ : relation 𝓁₁₂ʳ ⟪ A ⇒ B ⟫) {{R₁₂-Refl : Reflexive _R₁₂_}} {{R₁₂-Trans : Transitive _R₁₂_}}
  : Set (𝓁₁ ⊔ˡ 𝓁₁ʳ ⊔ˡ 𝓁₂ ⊔ˡ 𝓁₂ʳ ⊔ˡ 𝓁₁₂ʳ) where
  field
    ext[⇒] : ∀ {f g : ⟪ A ⇒ B ⟫} → (∀ {x : ⟪ A ⟫} → (f ⋅ x) R₂ (g ⋅ x)) → f R₁₂ g
open Extensional[⇒] {{...}} public

instance
  Extensional[⇒][⊑] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Extensional[⇒] (_⊑_ {A = A}) (_⊑_ {A = B}) (_⊑_ {A = A ⇒ B})
  Extensional[⇒][⊑] = record { ext[⇒] = ext[⇒]⸢⊑⸣ }
  Extensional[⇒][≈] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Extensional[⇒] (_≈_ {A = A}) (_≈_ {A = B}) (_≈_ {A = A ⇒ B})
  Extensional[⇒][≈] = record { ext[⇒] = ext[⇒]⸢≈⸣ }
