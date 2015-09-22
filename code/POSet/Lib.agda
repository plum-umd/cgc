module POSet.Lib where

open import Prelude
open import POSet.POSet
open import POSet.Fun
open import POSet.Power
open import POSet.Product
open import POSet.Classes

id⁺ : ∀ {𝓁} {A : POSet 𝓁} → ⟪ A ⇒ A ⟫
id⁺ = witness-x (curry⸢λ⸣ id⸢λ⸣) $ mk[witness] id id

flip⁺ : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} → ⟪ (A ⇒ B ⇒ C) ⇒ B ⇒ A ⇒ C ⟫
flip⁺ {A = A} {B} {C} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⇒ B ⇒ C ⟫ → ⟪ B ⟫ → ⟪ A ⟫ → ⟪ C ⟫
    fun f y x = f ⋅ x ⋅ y
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr f₁⊑f₂ x₁⊑x₂ y₁⊑y₂ = res-f-x[⇒] (res-f-x[⇒] f₁⊑f₂ y₁⊑y₂) x₁⊑x₂

infixr 9 _⊙_
_⊙_ : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} → ⟪ B ⇒ C ⟫ → ⟪ A ⇒ B ⟫ → ⟪ A ⇒ C ⟫
_⊙_ {A = A} {B} {C} g f = witness-x (curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ C ⟫
    fun x = g ⋅ (f ⋅ x)
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_) fun
      ppr x⊑y = res-x[⇒] {f = g} (res-x[⇒] {f = f} x⊑y)

[⊙] : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} → ⟪ (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C) ⟫
[⊙] {A = A} {B} {C} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ B ⇒ C ⟫ → ⟪ A ⇒ B ⟫ → ⟪ A ⇒ C ⟫
    fun g f = g ⊙ f
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr {g₁} {g₂} g₁⊑g₂ {f₁} {f₂} f₁⊑f₂ = ext[⇒]⸢⊑⸣ (res-f-x[⇒]⸢⊑⸣ g₁⊑g₂ (res-f[⇒]⸢⊑⸣ f₁⊑f₂))

right-unit[⊙] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f : ⟪ A ⇒ B ⟫} → f ⊙ id⁺ ≈ f
right-unit[⊙] = ext[⇒]⸢≈⸣ xRx⸢≈⸣

associative[⊙] : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} {D : POSet 𝓁₄} {h : ⟪ C ⇒ D ⟫} {g : ⟪ B ⇒ C ⟫} {f : ⟪ A ⇒ B ⟫} → (h ⊙ g) ⊙ f ≈ h ⊙ (g ⊙ f)
associative[⊙] = ext[⇒]⸢≈⸣ xRx⸢≈⸣

wrap : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} {D : POSet 𝓁₄} → ⟪ (C ⇒ D) ⇒ (A ⇒ B) ⇒ (B ⇒ C) ⇒ A ⇒ D ⟫
wrap {A = A} {B} {C} {D} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ C ⇒ D ⟫ → ⟪ A ⇒ B ⟫ → ⟪ B ⇒ C ⟫ → ⟪ A ⇒ D ⟫
    fun h f g = h ⊙ g ⊙ f
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr h₁⊑h₂ f₁⊑f₂ g₁⊑g₂ = ext[⇒]⸢⊑⸣ $ λ {x} → res-f-x[⇒]⸢⊑⸣ h₁⊑h₂ (res-f-x[⇒]⸢⊑⸣ g₁⊑g₂ (res-f[⇒]⸢⊑⸣ f₁⊑f₂))

[⋅] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ (A ⇒ B) ⇒ A ⇒ B ⟫
[⋅] {A = A} {B} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⇒ B ⟫ → ⟪ A ⟫ → ⟪ B ⟫
    fun = _⋅_
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr f⊑g x⊑y = res-f-x[⇒]⸢⊑⸣ f⊑g x⊑y

const⁺ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ A ⇒ B ⇒ A ⟫
const⁺ {A = A} {B} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ B ⟫ → ⟪ A ⟫
    fun = const
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr x⊑y _ = x⊑y

uncurry⁺ : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} → ⟪ (A ⇒ B ⇒ C) ⇒ A ×⁺ B ⇒ C ⟫
uncurry⁺ {A = A} {B} {C} = witness-x (curry⸢λ⸣ $ curry⸢λ↑⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⇒ B ⇒ C ⟫ → prod A B → ⟪ C ⟫
    fun f (x , y) = f ⋅ x ⋅ y
    abstract
      ppr : proper (_⊑_ ⇉ _⊴_ ⇉ _⊑_) fun
      ppr f⊑g (x₁⊑x₂ , y₁⊑y₂) = res-f-x[⇒]⸢⊑⸣ (res-f-x[⇒]⸢⊑⸣ f⊑g x₁⊑x₂) y₁⊑y₂

split⁺ : ∀ {𝓁} {A : POSet 𝓁} → ⟪ A ⇒ A ×⁺ A ⟫
split⁺ {A = A} = witness-x (curry⸢λ⸣ id⸢λ↑⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → prod A A
    fun x = x , x
    abstract
      ppr : proper (_⊑_ ⇉ _⊴_) fun
      ppr x⊑y = x⊑y , x⊑y

apply⸢×⁺⸣ : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} {D : POSet 𝓁₄} → ⟪ (A ⇒ B) ×⁺ (C ⇒ D) ⇒ A ×⁺ C ⇒ B ×⁺ D ⟫
apply⸢×⁺⸣ {𝓁₁} {𝓁₂} {𝓁₃} {𝓁₄} {A} {B} {C} {D} = witness-x (curry⸢λ↑⸣ $ curry⸢λ↑⸣ {𝓁₂ʳ = 𝓁₂ ⊔ˡ 𝓁₄} id⸢λ↑⸣) $ mk[witness] fun ppr
  where
    fun : prod (A ⇒ B) (C ⇒ D) → prod A C → prod B D
    fun (f , g) (x , y) = f ⋅ x , g ⋅ y
    abstract
      ppr : proper (_⊴_ ⇉ _⊴_ ⇉ _⊴_) fun
      ppr (f₁⊑f₂ , g₁⊑g₂) (x₁⊑x₂ , y₁⊑y₂) = res-f-x[⇒]⸢⊑⸣ f₁⊑f₂ x₁⊑x₂ , res-f-x[⇒]⸢⊑⸣ g₁⊑g₂ y₁⊑y₂
  
all⁺ : ∀ {𝓁} (A : POSet 𝓁) → ⟪ 𝒫 A ⟫
all⁺ {𝓁} A = witness-x id⸢ω⸣ $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → Set 𝓁
    fun = const $ lifted 𝓁 unit
    abstract
      ppr : proper (_⊒_ {A = A} ⇉ [→]) fun
      ppr = const id

all-in : ∀ {𝓁} {A : POSet 𝓁} {x : ⟪ A ⟫} → x ⋿ all⁺ A
all-in = Lift tt

empty⁺ : ∀ {𝓁} {A : POSet 𝓁} → ⟪ 𝒫 A ⟫
empty⁺ {𝓁} {A} = witness-x id⸢ω⸣ $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → Set 𝓁
    fun = const $ lifted 𝓁 void
    abstract
      ppr : proper (_⊑_ ⇉ [→]) fun
      ppr _ (Lift ())
