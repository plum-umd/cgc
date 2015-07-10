module OSet.GaloisConnection.IndependentAttributes where

open import Prelude
open import OSet.OSet
open import OSet.Fun
open import OSet.Power
open import OSet.Product
open import OSet.Lib
open import OSet.GaloisConnection.Classical
open import OSet.GaloisConnection.Constructive

α-fun⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ 𝒫 (A ⟨×⟩ B) ⟫ → prod (𝒫 A) (𝒫 B)
α-fun⸢IA⸣ XY = (pure ⋅ ↑π₁) * ⋅ XY , (pure ⋅ ↑π₂) * ⋅ XY

abstract
  monotonic[α-fun⸢IA⸣] : ∀ {𝓁} {A B : POSet 𝓁} → proper (_⊑_ ⇉ _⊴_) (α-fun⸢IA⸣ {A = A} {B})
  monotonic[α-fun⸢IA⸣] XY₁⊑XY₂ = res-x[λ]⸢⊑⸣ {f = (pure ⋅ ↑π₁) *} XY₁⊑XY₂ , res-x[λ]⸢⊑⸣ {f = (pure ⋅ ↑π₂) *} XY₁⊑XY₂

α⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ 𝒫 (A ⟨×⟩ B) ⇒ 𝒫 A ⟨×⟩ 𝒫 B ⟫
α⸢IA⸣ = witness-x (curry⸢λ⸣ id⸢λ↑⸣) $ mk[witness] α-fun⸢IA⸣ monotonic[α-fun⸢IA⸣]

data _∈γ⸢IA⸣_ {𝓁} {A B : POSet 𝓁} (xy : prod A B) (X,Y : prod (𝒫 A) (𝒫 B)) : Set 𝓁 where
  _,_  : π₁⸢prod⸣ xy ⋿ π₁⸢prod⸣ X,Y → π₂⸢prod⸣ xy ⋿ π₂⸢prod⸣ X,Y → xy ∈γ⸢IA⸣ X,Y

monotonic[∈γ⸢IA⸣] : ∀ {𝓁} {A B : POSet 𝓁} → proper (_⊴_ ⇉ _⊵_ ⇉ [→]) (flip $ _∈γ⸢IA⸣_ {A = A} {B})
monotonic[∈γ⸢IA⸣] (X₁⊑X₂ , Y₁⊑Y₂) (x₁⊒x₂ , y₁⊒y₂) (x₁∈X₁ , y₁∈Y₁) = res-X-x[ω]⸢⊑⸣ X₁⊑X₂ x₁⊒x₂ x₁∈X₁ , res-X-x[ω]⸢⊑⸣ Y₁⊑Y₂ y₁⊒y₂ y₁∈Y₁

γ⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ 𝒫 A ⟨×⟩ 𝒫 B ⇒ 𝒫 (A ⟨×⟩ B) ⟫
γ⸢IA⸣ = witness-x (curry⸢λ↑⸣ id⸢ω↑⸣) $ mk[witness] (flip _∈γ⸢IA⸣_) monotonic[∈γ⸢IA⸣]

sound⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} {XY : ⟪ 𝒫 (A ⟨×⟩ B) ⟫} → XY ⊑ γ⸢IA⸣ ⋅ (α⸢IA⸣ ⋅ XY)
sound⸢IA⸣ {A = A} {B} {XY} = ext[ω]⸢⊑⸣ P
  where
    P : ∀ {xy : ⟪ A ⟨×⟩ B ⟫} → xy ⋿ XY → xy ⋿ γ⸢IA⸣ ⋅ (α⸢IA⸣ ⋅ XY)
    P {↑⟨ x , y ⟩} xy∈XY = (∃𝒫 ↑ (x , y) ,, xy∈XY ,, xRx) , (∃𝒫 ↑ (x , y) ,, xy∈XY ,, xRx)

complete⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} {X,Y :  ⟪ 𝒫 A ⟨×⟩ 𝒫 B ⟫} → α⸢IA⸣ ⋅ (γ⸢IA⸣ ⋅ X,Y)  ⊑ X,Y
complete⸢IA⸣ {X,Y = ↑⟨ X , Y ⟩} = ↑⟨ ext[ω]⸢⊑⸣ LHS , ext[ω]⸢⊑⸣ RHS ⟩
  where
    LHS : ∀ {x} → x ⋿ (pure ⋅ ↑π₁) * ⋅ (γ⸢IA⸣ ⋅ ↑⟨ X , Y ⟩) → x ⋿ X
    LHS {x} (∃𝒫 ↑⟨ x' , y' ⟩ ,, x'∈X , y'∈Y ,, x'⊑x) = res-x[ω]⸢⊑⸣ {X = X} x'⊑x x'∈X
    RHS : ∀ {y} → y ⋿ (pure ⋅ ↑π₂) * ⋅ (γ⸢IA⸣ ⋅ ↑⟨ X , Y ⟩) → y ⋿ Y
    RHS {y} (∃𝒫 ↑⟨ x' , y' ⟩ ,, x'∈X , y'∈Y ,, y'⊑y) = res-x[ω]⸢⊑⸣ {X = Y} y'⊑y y'∈Y

⇄IA⇄ : ∀ {𝓁} {A B : POSet 𝓁} → 𝒫 (A ⟨×⟩ B) α⇄γ 𝒫 A ⟨×⟩ 𝒫 B
⇄IA⇄ = record
  { α[_] = α⸢IA⸣
  ; γ[_] = γ⸢IA⸣
  ; expansive[_] = π₂ expansive↔sound sound⸢IA⸣
  ; contractive[_] = π₂ contractive↔complete complete⸢IA⸣
  }

γ⸢IA⸣-exchange⸢ext⸣ :
  ∀ {𝓁} {A₁ A₂ B₁ B₂ : POSet 𝓁} (⇄A⇄ : A₁ η⇄γ A₂) (⇄B⇄ : B₁ η⇄γ B₂) {X^ Y^} {xy}
  → xy ⋿ γ⸢IA⸣ ⋅ (γ⸢η⸣[ ⇄A⇄ ] * ⋅ X^ ⟨,⟩ γ⸢η⸣[ ⇄B⇄ ] * ⋅ Y^)
  ↔ xy ⋿ γ⸢η⸣[ ⇄A⇄ ×⸢η⇄γ⸣ ⇄B⇄ ] * ⋅ (γ⸢IA⸣ ⋅ (X^ ⟨,⟩ Y^))
γ⸢IA⸣-exchange⸢ext⸣ ⇄A⇄ ⇄B⇄ {X^} {Y^} {↑⟨ x , y ⟩} = LHS , RHS
  where
    LHS : ↑⟨ x , y ⟩ ⋿ γ⸢IA⸣ ⋅ (γ⸢η⸣[ ⇄A⇄ ] * ⋅ X^ ⟨,⟩ γ⸢η⸣[ ⇄B⇄ ] * ⋅ Y^) → ↑⟨ x , y ⟩ ⋿ γ⸢η⸣[ ⇄A⇄ ×⸢η⇄γ⸣ ⇄B⇄ ] * ⋅ (γ⸢IA⸣ ⋅ (X^ ⟨,⟩ Y^))
    LHS ((∃𝒫 x^ ,, x^∈X^ ,, x∈γ[x^]) , (∃𝒫 y^ ,, y^∈Y^ ,, y∈γ[y^])) = ∃𝒫 ↑⟨ x^ , y^ ⟩ ,, x^∈X^ , y^∈Y^ ,, x∈γ[x^] , y∈γ[y^]
    RHS : ↑⟨ x , y ⟩ ⋿ γ⸢η⸣[ ⇄A⇄ ×⸢η⇄γ⸣ ⇄B⇄ ] * ⋅ (γ⸢IA⸣ ⋅ (X^ ⟨,⟩ Y^)) → ↑⟨ x , y ⟩ ⋿ γ⸢IA⸣ ⋅ (γ⸢η⸣[ ⇄A⇄ ] * ⋅ X^ ⟨,⟩ γ⸢η⸣[ ⇄B⇄ ] * ⋅ Y^)
    RHS (∃𝒫 ↑⟨ x^ , y^ ⟩ ,, x^∈X^ , y^∈Y^ ,, x∈γ[x^] , y∈γ[y^]) = (∃𝒫 x^ ,, x^∈X^ ,, x∈γ[x^]) , (∃𝒫 y^ ,, y^∈Y^ ,, y∈γ[y^])

exchange[γ⸢IA⸣] :
  ∀ {𝓁} {A₁ A₂ B₁ B₂ : POSet 𝓁} (⇄A⇄ : A₁ η⇄γ A₂) (⇄B⇄ : B₁ η⇄γ B₂) {X^ Y^}
  → γ⸢IA⸣ ⋅ (γ⸢η⸣[ ⇄A⇄ ] * ⋅ X^ ⟨,⟩ γ⸢η⸣[ ⇄B⇄ ] * ⋅ Y^)
  ≈ γ⸢η⸣[ ⇄A⇄ ×⸢η⇄γ⸣ ⇄B⇄ ] * ⋅ (γ⸢IA⸣ ⋅ (X^ ⟨,⟩ Y^))
exchange[γ⸢IA⸣] ⇄A⇄ ⇄B⇄ {X^} {Y^} = ext[ω]⸢≈⸣ $ λ {xy} → γ⸢IA⸣-exchange⸢ext⸣ ⇄A⇄ ⇄B⇄ {X^ = X^} {Y^} {xy}

unit[γ⸢IA⸣] : ∀ {𝓁} {A B : POSet 𝓁} {x : ⟪ A ⟫} {y : ⟪ B ⟫} → γ⸢IA⸣ ⋅ (return ⋅ x ⟨,⟩ return ⋅ y) ≈ return ⋅ (x ⟨,⟩ y)
unit[γ⸢IA⸣] {x = x} {y} = ext[ω]⸢≈⸣ $ λ {xy} → LHS {xy} , RHS {xy}
  where
    LHS : ∀ {xy} → xy ⋿ γ⸢IA⸣ ⋅ (return ⋅ x ⟨,⟩ return ⋅ y) → xy ⋿ return ⋅ (x ⟨,⟩ y)
    LHS {↑⟨ x' , y' ⟩} (x'⊑x , y'⊑y) = ↑⟨ x'⊑x , y'⊑y ⟩
    RHS : ∀ {xy} → xy ⋿ return ⋅ (x ⟨,⟩ y) → xy ⋿ γ⸢IA⸣ ⋅ (return ⋅ x ⟨,⟩ return ⋅ y)
    RHS {↑⟨ x' , y' ⟩} ↑⟨ x'⊑x , y'⊑y ⟩ = (x'⊑x , y'⊑y)
