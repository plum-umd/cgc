module POSet.GaloisConnection.IndependentAttributes where

open import Prelude
open import POSet.POSet
open import POSet.Fun
open import POSet.Power
open import POSet.Product
open import POSet.Lib
open import POSet.PowerMonad
open import POSet.GaloisConnection.Classical
open import POSet.GaloisConnection.Constructive

α⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ 𝒫 (A ×⁺ B) ⇒ 𝒫 A ×⁺ 𝒫 B ⟫
α⸢IA⸣ = witness-x (curry⸢λ⸣ id⸢λ↑⸣) $ mk[witness] fun ppr
  where
    fun : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ 𝒫 (A ×⁺ B) ⟫ → prod (𝒫 A) (𝒫 B)
    fun XY = (pure ⋅ π₁⁺) * ⋅ XY , (pure ⋅ π₂⁺) * ⋅ XY
    abstract
      ppr : ∀ {𝓁} {A B : POSet 𝓁} → proper (_⊑_ ⇉ _⊴_) (fun {A = A} {B})
      ppr XY₁⊑XY₂ = res-x[⇒]⸢⊑⸣ {f = (pure ⋅ π₁⁺) *} XY₁⊑XY₂ , res-x[⇒]⸢⊑⸣ {f = (pure ⋅ π₂⁺) *} XY₁⊑XY₂

data _∈γ⸢IA⸣_ {𝓁} {A B : POSet 𝓁} (xy : prod A B) (X,Y : prod (𝒫 A) (𝒫 B)) : Set 𝓁 where
  _,_  : π₁⸢prod⸣ xy ⋿ π₁⸢prod⸣ X,Y → π₂⸢prod⸣ xy ⋿ π₂⸢prod⸣ X,Y → xy ∈γ⸢IA⸣ X,Y

monotonic[∈γ]⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} → proper (_⊴_ ⇉ _⊵_ ⇉ [→]) (flip $ _∈γ⸢IA⸣_ {A = A} {B})
monotonic[∈γ]⸢IA⸣ (X₁⊑X₂ , Y₁⊑Y₂) (x₁⊒x₂ , y₁⊒y₂) (x₁∈X₁ , y₁∈Y₁) = res-X-x[𝒫]⸢⊑⸣ X₁⊑X₂ x₁⊒x₂ x₁∈X₁ , res-X-x[𝒫]⸢⊑⸣ Y₁⊑Y₂ y₁⊒y₂ y₁∈Y₁

γ⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ 𝒫 A ×⁺ 𝒫 B ⇒ 𝒫 (A ×⁺ B) ⟫
γ⸢IA⸣ = witness-x (curry⸢λ↑⸣ id⸢ω↑⸣) $ mk[witness] (flip _∈γ⸢IA⸣_) monotonic[∈γ]⸢IA⸣

sound⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} {XY : ⟪ 𝒫 (A ×⁺ B) ⟫} → XY ⊑ γ⸢IA⸣ ⋅ (α⸢IA⸣ ⋅ XY)
sound⸢IA⸣ {A = A} {B} {XY} = ext[𝒫]⸢⊑⸣ P
  where
    P : ∀ {xy : ⟪ A ×⁺ B ⟫} → xy ⋿ XY → xy ⋿ γ⸢IA⸣ ⋅ (α⸢IA⸣ ⋅ XY)
    P {↑⟨ x , y ⟩} xy∈XY = (∃𝒫 ↑ (x , y) ,, xy∈XY ,, xRx) , (∃𝒫 ↑ (x , y) ,, xy∈XY ,, xRx)

complete⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} {X,Y :  ⟪ 𝒫 A ×⁺ 𝒫 B ⟫} → α⸢IA⸣ ⋅ (γ⸢IA⸣ ⋅ X,Y)  ⊑ X,Y
complete⸢IA⸣ {X,Y = ↑⟨ X , Y ⟩} = ↑⟨ ext[𝒫]⸢⊑⸣ LHS , ext[𝒫]⸢⊑⸣ RHS ⟩
  where
    LHS : ∀ {x} → x ⋿ (pure ⋅ π₁⁺) * ⋅ (γ⸢IA⸣ ⋅ ↑⟨ X , Y ⟩) → x ⋿ X
    LHS {x} (∃𝒫 ↑⟨ x' , y' ⟩ ,, x'∈X , y'∈Y ,, x'⊑x) = res-x[𝒫]⸢⊑⸣ {X = X} x'⊑x x'∈X
    RHS : ∀ {y} → y ⋿ (pure ⋅ π₂⁺) * ⋅ (γ⸢IA⸣ ⋅ ↑⟨ X , Y ⟩) → y ⋿ Y
    RHS {y} (∃𝒫 ↑⟨ x' , y' ⟩ ,, x'∈X , y'∈Y ,, y'⊑y) = res-x[𝒫]⸢⊑⸣ {X = Y} y'⊑y y'∈Y

⇄IA⇄ : ∀ {𝓁} {A B : POSet 𝓁} → 𝒫 (A ×⁺ B) ⇄ 𝒫 A ×⁺ 𝒫 B
⇄IA⇄ = record
  { α[_] = α⸢IA⸣
  ; γ[_] = γ⸢IA⸣
  ; expansive[_] = π₂ expansive↔sound sound⸢IA⸣
  ; contractive[_] = π₂ contractive↔complete complete⸢IA⸣
  }

homomorphic[γ/γ]⸢IA-ext⸣[_,_] :
  ∀ {𝓁} {A₁ A₂ B₁ B₂ : POSet 𝓁} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) {X♯ Y♯} {xy}
  → xy ⋿ γ⸢IA⸣ ⋅ (γᶜ[ ⇄A⇄ ] * ⋅ X♯ ,⁺ γᶜ[ ⇄B⇄ ] * ⋅ Y♯)
  ↔ xy ⋿ γᶜ[ ⇄A⇄ ×⸢⇄ᶜ⸣ ⇄B⇄ ] * ⋅ (γ⸢IA⸣ ⋅ (X♯ ,⁺ Y♯))
homomorphic[γ/γ]⸢IA-ext⸣[ ⇄A⇄ , ⇄B⇄ ] {X♯} {Y♯} {↑⟨ x , y ⟩} = LHS , RHS
  where
    LHS : ↑⟨ x , y ⟩ ⋿ γ⸢IA⸣ ⋅ (γᶜ[ ⇄A⇄ ] * ⋅ X♯ ,⁺ γᶜ[ ⇄B⇄ ] * ⋅ Y♯) → ↑⟨ x , y ⟩ ⋿ γᶜ[ ⇄A⇄ ×⸢⇄ᶜ⸣ ⇄B⇄ ] * ⋅ (γ⸢IA⸣ ⋅ (X♯ ,⁺ Y♯))
    LHS ((∃𝒫 x♯ ,, x♯∈X♯ ,, x∈γ[x♯]) , (∃𝒫 y♯ ,, y♯∈Y♯ ,, y∈γ[y♯])) = ∃𝒫 ↑⟨ x♯ , y♯ ⟩ ,, x♯∈X♯ , y♯∈Y♯ ,, x∈γ[x♯] , y∈γ[y♯]
    RHS : ↑⟨ x , y ⟩ ⋿ γᶜ[ ⇄A⇄ ×⸢⇄ᶜ⸣ ⇄B⇄ ] * ⋅ (γ⸢IA⸣ ⋅ (X♯ ,⁺ Y♯)) → ↑⟨ x , y ⟩ ⋿ γ⸢IA⸣ ⋅ (γᶜ[ ⇄A⇄ ] * ⋅ X♯ ,⁺ γᶜ[ ⇄B⇄ ] * ⋅ Y♯)
    RHS (∃𝒫 ↑⟨ x♯ , y♯ ⟩ ,, x♯∈X♯ , y♯∈Y♯ ,, x∈γ[x♯] , y∈γ[y♯]) = (∃𝒫 x♯ ,, x♯∈X♯ ,, x∈γ[x♯]) , (∃𝒫 y♯ ,, y♯∈Y♯ ,, y∈γ[y♯])

homomorphic[γ/γ]⸢IA⸣[_,_] :
  ∀ {𝓁} {A₁ A₂ B₁ B₂ : POSet 𝓁} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) {X♯ Y♯}
  → γ⸢IA⸣ ⋅ (γᶜ[ ⇄A⇄ ] * ⋅ X♯ ,⁺ γᶜ[ ⇄B⇄ ] * ⋅ Y♯)
  ≈ γᶜ[ ⇄A⇄ ×⸢⇄ᶜ⸣ ⇄B⇄ ] * ⋅ (γ⸢IA⸣ ⋅ (X♯ ,⁺ Y♯))
homomorphic[γ/γ]⸢IA⸣[ ⇄A⇄ , ⇄B⇄ ] {X♯} {Y♯} = ext[𝒫]⸢≈⸣ $ λ {xy} → homomorphic[γ/γ]⸢IA-ext⸣[ ⇄A⇄ , ⇄B⇄ ] {X♯ = X♯} {Y♯} {xy}

homomorphic[γ/return]⸢IA⸣ : ∀ {𝓁} {A B : POSet 𝓁} {x : ⟪ A ⟫} {y : ⟪ B ⟫} → γ⸢IA⸣ ⋅ (return ⋅ x ,⁺ return ⋅ y) ≈ return ⋅ (x ,⁺ y)
homomorphic[γ/return]⸢IA⸣ {x = x} {y} = ext[𝒫]⸢≈⸣ $ λ {xy} → LHS {xy} , RHS {xy}
  where
    LHS : ∀ {xy} → xy ⋿ γ⸢IA⸣ ⋅ (return ⋅ x ,⁺ return ⋅ y) → xy ⋿ return ⋅ (x ,⁺ y)
    LHS {↑⟨ x' , y' ⟩} (x'⊑x , y'⊑y) = ↑⟨ x'⊑x , y'⊑y ⟩
    RHS : ∀ {xy} → xy ⋿ return ⋅ (x ,⁺ y) → xy ⋿ γ⸢IA⸣ ⋅ (return ⋅ x ,⁺ return ⋅ y)
    RHS {↑⟨ x' , y' ⟩} ↑⟨ x'⊑x , y'⊑y ⟩ = (x'⊑x , y'⊑y)
