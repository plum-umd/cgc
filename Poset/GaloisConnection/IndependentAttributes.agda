module Poset.GaloisConnection.IndependentAttributes where

open import Prelude
open import Poset.Poset
open import Poset.Fun
open import Poset.Power
open import Poset.Product
open import Poset.Lib
open import Poset.PowerMonad
open import Poset.GaloisConnection.Classical
open import Poset.GaloisConnection.Constructive

infixr 3 _,_

α⸢IA⸣ : ∀ {ℓ} {A B : Poset ℓ} → ⟪ ℘ (A ∧♮ B) ↗ ℘ A ∧♮ ℘ B ⟫
α⸢IA⸣ = witness (curry⸢λ⸣ id⸢λ♭⸣) $ mk[witness] fun ppr
  where
    fun : ∀ {ℓ} {A B : Poset ℓ} → ⟪ ℘ (A ∧♮ B) ⟫ → (℘ A) ∧♭ (℘ B)
    fun XY = (pure ⋅ π₁♮) *♮ ⋅ XY , (pure ⋅ π₂♮) *♮ ⋅ XY
    abstract
      ppr : ∀ {ℓ} {A B : Poset ℓ} → proper (_⊑♮_ ⇉ _≼_) (fun {A = A} {B})
      ppr XY₁⊑XY₂ = res[x]⸢⊑↗⸣ {f = (pure ⋅ π₁♮) *♮} XY₁⊑XY₂ , res[x]⸢⊑↗⸣ {f = (pure ⋅ π₂♮) *♮} XY₁⊑XY₂

data _∈γ⸢IA⸣_ {ℓ} {A B : Poset ℓ} (xy : A ∧♭ B) (X,Y : (℘ A) ∧♭ (℘ B)) : Set ℓ where
  _,_ : π₁⸢∧♭⸣ xy ⋿ π₁⸢∧♭⸣ X,Y → π₂⸢∧♭⸣ xy ⋿ π₂⸢∧♭⸣ X,Y → xy ∈γ⸢IA⸣ X,Y

monotonic[∈γ]⸢IA⸣ : ∀ {ℓ} {A B : Poset ℓ} → proper (_≼_ ⇉ _≽_ ⇉ [→]) (flip $ _∈γ⸢IA⸣_ {A = A} {B})
monotonic[∈γ]⸢IA⸣ (X₁⊑X₂ , Y₁⊑Y₂) (x₁⊒x₂ , y₁⊒y₂) (x₁∈X₁ , y₁∈Y₁) = res[Xx]⸢⊑℘⸣ X₁⊑X₂ x₁⊒x₂ x₁∈X₁ , res[Xx]⸢⊑℘⸣ Y₁⊑Y₂ y₁⊒y₂ y₁∈Y₁

γ⸢IA⸣ : ∀ {ℓ} {A B : Poset ℓ} → ⟪ ℘ A ∧♮ ℘ B ↗ ℘ (A ∧♮ B) ⟫
γ⸢IA⸣ = witness (curry⸢λ♭⸣ id⸢ω♭⸣) $ mk[witness] (flip _∈γ⸢IA⸣_) monotonic[∈γ]⸢IA⸣

sound⸢IA⸣ : ∀ {ℓ} {A B : Poset ℓ} {XY : ⟪ ℘ (A ∧♮ B) ⟫} → XY ⊑♮ γ⸢IA⸣ ⋅ (α⸢IA⸣ ⋅ XY)
sound⸢IA⸣ {A = A} {B} {XY} = ext⸢⊑℘⸣ P
  where
    P : ∀ {xy : ⟪ A ∧♮ B ⟫} → xy ⋿ XY → xy ⋿ γ⸢IA⸣ ⋅ (α⸢IA⸣ ⋅ XY)
    P {♮⟨ x , y ⟩} xy∈XY = (∃℘ ♮ (x , y) ,, xy∈XY ,, xRx) , (∃℘ ♮ (x , y) ,, xy∈XY ,, xRx)

complete⸢IA⸣ : ∀ {ℓ} {A B : Poset ℓ} {X,Y :  ⟪ ℘ A ∧♮ ℘ B ⟫} → α⸢IA⸣ ⋅ (γ⸢IA⸣ ⋅ X,Y) ⊑♮ X,Y
complete⸢IA⸣ {X,Y = ♮⟨ X , Y ⟩} = ♮⟨ ext⸢⊑℘⸣ LHS , ext⸢⊑℘⸣ RHS ⟩
  where
    LHS : ∀ {x} → x ⋿ (pure ⋅ π₁♮) *♮ ⋅ (γ⸢IA⸣ ⋅ ♮⟨ X , Y ⟩) → x ⋿ X
    LHS {x} (∃℘ ♮⟨ x' , y' ⟩ ,, x'∈X , y'∈Y ,, x'⊑x) = res[x]⸢⊑℘⸣ {X = X} x'⊑x x'∈X
    RHS : ∀ {y} → y ⋿ (pure ⋅ π₂♮) *♮ ⋅ (γ⸢IA⸣ ⋅ ♮⟨ X , Y ⟩) → y ⋿ Y
    RHS {y} (∃℘ ♮⟨ x' , y' ⟩ ,, x'∈X , y'∈Y ,, y'⊑y) = res[x]⸢⊑℘⸣ {X = Y} y'⊑y y'∈Y

⇄IA⇄ : ∀ {ℓ} {A B : Poset ℓ} → ℘ (A ∧♮ B) ⇄ ℘ A ∧♮ ℘ B
⇄IA⇄ = record
  { α[_] = α⸢IA⸣
  ; γ[_] = γ⸢IA⸣
  ; extensive[_] = π₂ ⟦extensive⟧ sound⸢IA⸣
  ; reductive[_] = π₂ ⟦reductive⟧ complete⸢IA⸣
  }

homomorphic[γγ/ext]⸢IA⸣[_,_] :
  ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) {X♯ Y♯} {xy}
  → xy ⋿ γ⸢IA⸣ ⋅ (γᶜ[ ⇄A⇄ ] *♮ ⋅ X♯ ,♮ γᶜ[ ⇄B⇄ ] *♮ ⋅ Y♯)
  ↔ xy ⋿ γᶜ[ ⇄A⇄ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] *♮ ⋅ (γ⸢IA⸣ ⋅ (X♯ ,♮ Y♯))
homomorphic[γγ/ext]⸢IA⸣[ ⇄A⇄ , ⇄B⇄ ] {X♯} {Y♯} {♮⟨ x , y ⟩} = LHS , RHS
  where
    LHS : ♮⟨ x , y ⟩ ⋿ γ⸢IA⸣ ⋅ (γᶜ[ ⇄A⇄ ] *♮ ⋅ X♯ ,♮ γᶜ[ ⇄B⇄ ] *♮ ⋅ Y♯) → ♮⟨ x , y ⟩ ⋿ γᶜ[ ⇄A⇄ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] *♮ ⋅ (γ⸢IA⸣ ⋅ (X♯ ,♮ Y♯))
    LHS ((∃℘ x♯ ,, x♯∈X♯ ,, x∈γ[x♯]) , (∃℘ y♯ ,, y♯∈Y♯ ,, y∈γ[y♯])) = ∃℘ ♮⟨ x♯ , y♯ ⟩ ,, x♯∈X♯ , y♯∈Y♯ ,, x∈γ[x♯] , y∈γ[y♯]
    RHS : ♮⟨ x , y ⟩ ⋿ γᶜ[ ⇄A⇄ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] *♮ ⋅ (γ⸢IA⸣ ⋅ (X♯ ,♮ Y♯)) → ♮⟨ x , y ⟩ ⋿ γ⸢IA⸣ ⋅ (γᶜ[ ⇄A⇄ ] *♮ ⋅ X♯ ,♮ γᶜ[ ⇄B⇄ ] *♮ ⋅ Y♯)
    RHS (∃℘ ♮⟨ x♯ , y♯ ⟩ ,, x♯∈X♯ , y♯∈Y♯ ,, x∈γ[x♯] , y∈γ[y♯]) = (∃℘ x♯ ,, x♯∈X♯ ,, x∈γ[x♯]) , (∃℘ y♯ ,, y♯∈Y♯ ,, y∈γ[y♯])

homomorphic[γγ]⸢IA⸣[_,_] :
  ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) {X♯ Y♯}
  → γ⸢IA⸣ ⋅ (γᶜ[ ⇄A⇄ ] *♮ ⋅ X♯ ,♮ γᶜ[ ⇄B⇄ ] *♮ ⋅ Y♯)
  ≈♮ γᶜ[ ⇄A⇄ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] *♮ ⋅ (γ⸢IA⸣ ⋅ (X♯ ,♮ Y♯))
homomorphic[γγ]⸢IA⸣[ ⇄A⇄ , ⇄B⇄ ] {X♯} {Y♯} = ext⸢≈℘⸣ $ λ {xy} → homomorphic[γγ/ext]⸢IA⸣[ ⇄A⇄ , ⇄B⇄ ] {X♯ = X♯} {Y♯} {xy}

homomorphic[γreturn]⸢IA⸣ : ∀ {ℓ} {A B : Poset ℓ} {x : ⟪ A ⟫} {y : ⟪ B ⟫} → γ⸢IA⸣ ⋅ (return♮ ⋅ x ,♮ return♮ ⋅ y) ≈♮ return♮ ⋅ (x ,♮ y)
homomorphic[γreturn]⸢IA⸣ {x = x} {y} = ext⸢≈℘⸣ $ λ {xy} → LHS {xy} , RHS {xy}
  where
    LHS : ∀ {xy} → xy ⋿ γ⸢IA⸣ ⋅ (return♮ ⋅ x ,♮ return♮ ⋅ y) → xy ⋿ return♮ ⋅ (x ,♮ y)
    LHS {♮⟨ x' , y' ⟩} (x'⊑x , y'⊑y) = ♮⟨ x'⊑x , y'⊑y ⟩
    RHS : ∀ {xy} → xy ⋿ return♮ ⋅ (x ,♮ y) → xy ⋿ γ⸢IA⸣ ⋅ (return♮ ⋅ x ,♮ return♮ ⋅ y)
    RHS {♮⟨ x' , y' ⟩} ♮⟨ x'⊑x , y'⊑y ⟩ = (x'⊑x , y'⊑y)
