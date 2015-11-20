module POSet.Product where

open import Prelude
open import POSet.POSet
open import POSet.Fun

infixr 3 _,_
data prod {𝓁₁ 𝓁₂} (A : POSet 𝓁₁) (B : POSet 𝓁₂) : Set (𝓁₁ ⊔ˡ 𝓁₂) where
  _,_ : ⟪ A ⟫ → ⟪ B ⟫ → prod A B

π₁⸢prod⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → prod A B → ⟪ A ⟫
π₁⸢prod⸣ (x , _) = x

π₂⸢prod⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → prod A B → ⟪ B ⟫
π₂⸢prod⸣ (_ , y) = y

infix 8 _⊴⸢prod⸣_
data _⊴⸢prod⸣_ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} : relation (𝓁₁ ⊔ˡ 𝓁₂) (prod A B) where
  _,_ : ∀ {x₁ x₂ y₁ y₂} → x₁ ⊑ x₂ → y₁ ⊑ y₂ → (x₁ , y₁) ⊴⸢prod⸣ (x₂ , y₂)

xRx⸢⊴⸢prod⸣⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → reflexive (_⊴⸢prod⸣_ {A = A} {B})
xRx⸢⊴⸢prod⸣⸣ {x = x , y} = xRx , xRx

infixr 9 _⌾⸢⊴⸢prod⸣⸣_
_⌾⸢⊴⸢prod⸣⸣_ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → transitive (_⊴⸢prod⸣_ {A = A} {B})
(x₂⊑x₃ , y₂⊑y₃) ⌾⸢⊴⸢prod⸣⸣ (x₁⊑x₂ , y₁⊑y₂) = (x₂⊑x₃ ⌾ x₁⊑x₂) , (y₂⊑y₃ ⌾ y₁⊑y₂)

instance
  Reflexive[⊴⸢prod⸣] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Reflexive (_⊴⸢prod⸣_ {A = A} {B})
  Reflexive[⊴⸢prod⸣] = record { xRx = xRx⸢⊴⸢prod⸣⸣ }
  Transitive[⊴⸢prod⸣] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Transitive (_⊴⸢prod⸣_ {A = A} {B})
  Transitive[⊴⸢prod⸣] = record { _⌾_ = _⌾⸢⊴⸢prod⸣⸣_ }
  PreOrder[prod] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → PreOrder (𝓁₁ ⊔ˡ 𝓁₂) (prod A B)
  PreOrder[prod] = record { _⊴_ = _⊴⸢prod⸣_ }

infixr 6 _×⁺_
_×⁺_ : ∀ {𝓁₁ 𝓁₂} → POSet 𝓁₁ → POSet 𝓁₂ → POSet (𝓁₁ ⊔ˡ 𝓁₂)
A ×⁺ B = ⇧ (prod A B)

[,] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ A ⇒ B ⇒ A ×⁺ B ⟫
[,] {𝓁₁} {𝓁₂} {A = A} {B} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ {𝓁₂ʳ = 𝓁₁ ⊔ˡ 𝓁₂} id⸢λ↑⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ B ⟫ → prod A B
    fun = _,_
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊴_) fun
      ppr x₁⊑x₂ y₁⊑y₂ = x₁⊑x₂ , y₁⊑y₂

infixr 3 _,⁺_
_,⁺_ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ A ⟫ → ⟪ B ⟫ → ⟪ A ×⁺ B ⟫
x ,⁺ y = [,] ⋅ x ⋅ y

π₁⁺ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ A ×⁺ B ⇒ A ⟫
π₁⁺ {A = A} {B} = witness-x (curry⸢λ↑⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : prod A B → ⟪ A ⟫
    fun (x , _) = x
    abstract
      ppr : proper (_⊴_ ⇉ _⊑_) fun
      ppr (x₁⊑x₂ , _) = x₁⊑x₂

π₂⁺ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ A ×⁺ B ⇒ B ⟫
π₂⁺ {A = A} {B} = witness-x (curry⸢λ↑⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : prod A B → ⟪ B ⟫
    fun (_ , y) = y
    abstract
      ppr : proper (_⊴_ ⇉ _⊑_) fun
      ppr (_ , y₁⊑y₂) = y₁⊑y₂
