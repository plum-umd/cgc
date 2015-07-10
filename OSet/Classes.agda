module OSet.Classes where

open import Prelude
open import OSet.OSet
open import OSet.Fun
open import OSet.Power

record Logical[λ]
  {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ 𝓁₁₂ʳ} {A : POSet 𝓁₁} {B : POSet 𝓁₂}
  (_R₁_ : relation 𝓁₁ʳ ⟪ A ⟫) {{R₁-Refl : Reflexive _R₁_}} {{R₁-Trans : Transitive _R₁_}}
  (_R₂_ : relation 𝓁₂ʳ ⟪ B ⟫) {{R₂-Refl : Reflexive _R₂_}} {{R₂-Trans : Transitive _R₂_}}
  (_R₁₂_ : relation 𝓁₁₂ʳ ⟪ A ⇒ B ⟫) {{R₁₂-Refl : Reflexive _R₁₂_}} {{R₁₂-Trans : Transitive _R₁₂_}}
  : Set (𝓁₁ ⊔ˡ 𝓁₁ʳ ⊔ˡ 𝓁₂ ⊔ˡ 𝓁₂ʳ ⊔ˡ 𝓁₁₂ʳ) where
  field
    res-f-x[λ] : ∀ {f g : ⟪ A ⇒ B ⟫} {x y : ⟪ A ⟫} → f R₁₂ g → x R₁ y → (f ⋅ x) R₂ (g ⋅ y)
  res-x[λ] : ∀ {f : ⟪ A ⇒ B ⟫} {x y : ⟪ A ⟫} → x R₁ y → (f ⋅ x) R₂ (f ⋅ y)
  res-x[λ] {f} = res-f-x[λ] (xRx {x = f})
  res-f[λ] : ∀ {f g : ⟪ A ⇒ B ⟫} {x : ⟪ A ⟫} → f R₁₂ g → (f ⋅ x) R₂ (g ⋅ x)
  res-f[λ] f₁Rf₂ = res-f-x[λ] f₁Rf₂ xRx
open Logical[λ] {{...}} public

instance
  Logical[λ][≡] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical[λ] (_≡_ {A = ⟪ A ⟫}) (_≡_ {A = ⟪ B ⟫}) (_≡_ {A = ⟪ A ⇒ B ⟫})
  Logical[λ][≡] = record { res-f-x[λ] = res2-xy }
  Logical[λ][⊑] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical[λ] (_⊑_ {A = ⟪ A ⟫}) (_⊑_ {A = ⟪ B ⟫}) (_⊑_ {A = ⟪ A ⇒ B ⟫})
  Logical[λ][⊑] = record { res-f-x[λ] = res-f-x[λ]⸢⊑⸣ }
  Logical[λ][≈] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical[λ] (_≈_ {A = ⟪ A ⟫}) (_≈_ {A = ⟪ B ⟫}) (_≈_ {A = ⟪ A ⇒ B ⟫})
  Logical[λ][≈] = record { res-f-x[λ] = res-f-x[λ]⸢≈⸣ }

record Extensional[λ]
  {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ 𝓁₁₂ʳ} {A : POSet 𝓁₁} {B : POSet 𝓁₂}
  (_R₁_ : relation 𝓁₁ʳ ⟪ A ⟫) {{R₁-Refl : Reflexive _R₁_}} {{R₁-Trans : Transitive _R₁_}}
  (_R₂_ : relation 𝓁₂ʳ ⟪ B ⟫) {{R₂-Refl : Reflexive _R₂_}} {{R₂-Trans : Transitive _R₂_}}
  (_R₁₂_ : relation 𝓁₁₂ʳ ⟪ A ⇒ B ⟫) {{R₁₂-Refl : Reflexive _R₁₂_}} {{R₁₂-Trans : Transitive _R₁₂_}}
  : Set (𝓁₁ ⊔ˡ 𝓁₁ʳ ⊔ˡ 𝓁₂ ⊔ˡ 𝓁₂ʳ ⊔ˡ 𝓁₁₂ʳ) where
  field
    ext[λ] : ∀ {f g : ⟪ A ⇒ B ⟫} → (∀ {x : ⟪ A ⟫} → (f ⋅ x) R₂ (g ⋅ x)) → f R₁₂ g
open Extensional[λ] {{...}} public

instance
  Extensional[λ][⊑] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Extensional[λ] (_⊑_ {A = ⟪ A ⟫}) (_⊑_ {A = ⟪ B ⟫}) (_⊑_ {A = ⟪ A ⇒ B ⟫})
  Extensional[λ][⊑] = record { ext[λ] = ext[λ]⸢⊑⸣ }
  Extensional[λ][≈] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Extensional[λ] (_≈_ {A = ⟪ A ⟫}) (_≈_ {A = ⟪ B ⟫}) (_≈_ {A = ⟪ A ⇒ B ⟫})
  Extensional[λ][≈] = record { ext[λ] = ext[λ]⸢≈⸣ }

-- Need to make a typeclass instance for ⊴ on Set so it can be `→` for
-- `⊑` and `↔` for `≈`. Sounds like it might fall apart, so punting on
-- these generic defs for now...

-- record Logical[ω]
--   {𝓁 𝓁ʳ 𝓁'ʳ} {A : POSet 𝓁}
--   (_R_ : relation 𝓁ʳ ⟪ A ⟫) {{R-Refl : Reflexive _R_}} {{R-Trans : Transitive _R_}}
--   (_R'_ : relation 𝓁'ʳ ⟪ 𝒫 A ⟫) {{R'-Refl : Reflexive _R'_}} {{R'-Trans : Transitive _R'_}}
--   : Set (sucˡ 𝓁 ⊔ˡ 𝓁ʳ ⊔ˡ 𝓁'ʳ) where
--   field
--     res-X-x[ω] : ∀ {X Y : ⟪ 𝒫 A ⟫} {x y : ⟪ A ⟫} → X R' Y → y R x → x ⋿ X → y ⋿ Y
--   res-x[ω] : ∀ {X : ⟪ 𝒫 A ⟫} {x y : ⟪ A ⟫} → y R x → x ⋿ X → y ⋿ X
--   res-x[ω] {X} = res-X-x[ω] (xRx {x = X})
--   res-X[ω] : ∀ {X Y : ⟪ 𝒫 A ⟫} {x : ⟪ A ⟫} → X R' Y → x ⋿ X → x ⋿ Y
--   res-X[ω] f₁Rf₂ = res-X-x[ω] f₁Rf₂ xRx
-- open Logical[ω] {{...}} public
-- 
-- instance
--   Logical[ω][≡] : ∀ {𝓁} {A : POSet 𝓁} → Logical[ω] (_≡_ {A = ⟪ A ⟫}) (_≡_ {A = ⟪ 𝒫 A ⟫})
--   Logical[ω][≡] = record { res-X-x[ω] = ? } -- res2-xy }
--   Logical[ω][⊑] : ∀ {𝓁} {A : POSet 𝓁} → Logical[ω] (_⊑_ {A = ⟪ A ⟫}) (_⊑_ {A = ⟪ 𝒫 A ⟫})
--   Logical[ω][⊑] = record { res-X-x[ω] = res-X-x[ω]⸢⊑⸣ }
--   Logical[ω][≈] : ∀ {𝓁} {A : POSet 𝓁} → Logical[ω] (_≈_ {A = ⟪ A ⟫}) (_≈_ {A = ⟪ 𝒫 A ⟫})
--   Logical[ω][≈] = record { res-X-x[ω] = res-X-x[ω]⸢≈⸣ }
-- 
-- record Extensional[ω]
--   {𝓁₁ 𝓁₁ʳ 𝓁₁'ʳ} {A : POSet 𝓁₁}
--   (_R₁_ : relation 𝓁₁ʳ ⟪ A ⟫) {{R₁-Refl : Reflexive _R₁_}} {{R₁-Trans : Transitive _R₁_}}
--   (_R₁'_ : relation 𝓁₁'ʳ ⟪ 𝒫 A ⟫) {{R₁₂-Refl : Reflexive _R₁'_}} {{R₁₂-Trans : Transitive _R₁'_}}
--   : Set (sucˡ 𝓁₁ ⊔ˡ 𝓁₁ʳ ⊔ˡ 𝓁₁'ʳ) where
--   field
--     ext[ω] : ∀ {X Y : ⟪ 𝒫 A ⟫} → (∀ {x : ⟪ A ⟫} → x ⋿ X → x ⋿ Y) → X R₁' Y
-- open Extensional[ω] {{...}} public
