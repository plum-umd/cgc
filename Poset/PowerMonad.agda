module Poset.PowerMonad where

open import Prelude
open import Poset.Poset
open import Poset.Fun
open import Poset.Power
open import Poset.ProofMode
open import Poset.Lib

infixr 2 ∃℘_,,_,,_
infixr 10 Σ℘
infixr 30 _⟐_
infixl 60 _*♮

return♮ : ∀ {ℓ} {A : Poset ℓ} → ⟪ A ↗ ℘ A ⟫
return♮ {ℓ} {A} = witness (curry⸢λ⸣ id⸢ω⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ A ⟫ → Set ℓ
    fun x y = y ⊑♮ x
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊒♮_ ⇉ [→]) fun
      ppr x₁⊑x₂ y₁⊒y₂ x₁∈X₁ = x₁⊑x₂ ⊚ x₁∈X₁ ⊚ y₁⊒y₂

⟦return⊑X⟧ : ∀ {ℓ} {A : Poset ℓ} {x : ⟪ A ⟫} {X : ⟪ ℘ A ⟫} → return♮ ⋅ x ⊑♮ X ↔ x ⋿ X
⟦return⊑X⟧ {x = x} {X} =  (λ return[x]⊑X → res[X]⸢⊑℘⸣ return[x]⊑X xRx) , (λ x∈X → ext⸢⊑℘⸣ (λ x⊒y → res[x]⸢⊑℘⸣ {X = X} x⊒y x∈X))

ext⸢⊑℘/return⸣ : ∀ {ℓ} {A : Poset ℓ} {X Y : ⟪ ℘ A ⟫} → (∀ {x} → return♮ ⋅ x ⊑♮ X → return♮ ⋅ x ⊑♮ Y) → X ⊑♮ Y
ext⸢⊑℘/return⸣ X⊑Y = ext⸢⊑℘⸣ $ π₁ ⟦return⊑X⟧ ∘ X⊑Y ∘ π₂ ⟦return⊑X⟧

ext⸢≈℘/return⸣ : ∀ {ℓ} {A : Poset ℓ} {X Y : ⟪ ℘ A ⟫} → (∀ {x} → return♮ ⋅ x ⊑♮ X ↔ return♮ ⋅ x ⊑♮ Y) → X ≈♮ Y
ext⸢≈℘/return⸣ {X = X} {Y} X≈Y = ext⸢≈℘⸣ $ π₁ ⟦return⊑X⟧ ∘ π₁ X≈Y ∘ π₂ ⟦return⊑X⟧ , π₁ ⟦return⊑X⟧ ∘ π₂ X≈Y ∘ π₂ ⟦return⊑X⟧

pure : ∀ {ℓ} {A B : Poset ℓ} → ⟪ (A ↗ B) ↗ (A ↗ ℘ B) ⟫
pure = [∘♮] ⋅ return♮

injective[pure]⸢⊑⸣ : ∀ {ℓ} {A B : Poset ℓ} {f g : ⟪ A ↗ B ⟫} → pure ⋅ f ⊑♮ pure ⋅ g → f ⊑♮ g
injective[pure]⸢⊑⸣ pure[f]⊑pure[g] = ext⸢⊑↗⸣ $ π₁ ⟦return⊑X⟧ (res[f]⸢⊑↗⸣ pure[f]⊑pure[g])
  
homomorphic[pure/ext] : ∀ {ℓ} {A B C : Poset ℓ} {g : ⟪ B ↗ C ⟫} {f : ⟪ A ↗ B ⟫} → pure ⋅ (g ∘♮ f) ≈♮ pure ⋅ g ∘♮ f
homomorphic[pure/ext] = ◇ associative[∘♮]

homomorphic[pure] : ∀ {ℓ} {A B C : Poset ℓ} {g : ⟪ B ↗ C ⟫} {f : ⟪ A ↗ B ⟫} {x : ⟪ A ⟫} → pure ⋅ (g ∘♮ f) ⋅ x ≈♮ pure ⋅ g ⋅ (f ⋅ x)
homomorphic[pure] {g = g} {f} = res[f]⸢≈↗⸣ $ homomorphic[pure/ext] {g = g} {f}

syntax Σ℘ X (λ x → P) = ∃℘ x ⋿ X 𝑠𝑡 P
record Σ℘ {ℓ} {A : Poset ℓ} (X : ⟪ ℘ A ⟫) (P : ⟪ A ⟫ → Set ℓ) : Set ℓ where
  constructor ∃℘_,,_,,_
  field
    x : ⟪ A ⟫
    x∈X : x ⋿ X
    P[x] : P x
      
_*♮ : ∀ {ℓ} {A B : Poset ℓ} → ⟪ A ↗ ℘ B ⟫ → ⟪ ℘ A ↗ ℘ B ⟫
_*♮ {ℓ} {A} {B} f = witness (curry⸢λ⸣ id⸢ω⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ ℘ A ⟫ → ⟪ B ⟫ → Set ℓ
    fun X y = Σ℘ X (λ x → y ⋿ f ⋅ x)
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊒♮_ ⇉ [→]) fun
      ppr X⊑Y x⊒y (∃℘ z ,, z∈X ,, x∈f[z]) = ∃℘ z ,, res[X]⸢⊑℘⸣ X⊑Y z∈X ,, res[x]⸢⊑℘⸣ {X = f ⋅ z} x⊒y x∈f[z]

[*] : ∀ {ℓ} {A B : Poset ℓ} → ⟪ (A ↗ ℘ B) ↗ (℘ A ↗ ℘ B) ⟫
[*] {ℓ} {A} {B} = witness (curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ↗ ℘ B ⟫ → ⟪ ℘ A ↗ ℘ B ⟫
    fun f = f *♮
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_) fun
      ppr {f} {g} f⊑g = ext⸢⊑↗⸣ $ ext⸢⊑℘⸣ H
        where
          H : ∀ {X y} → ∃℘ x ⋿ X 𝑠𝑡 y ⋿ f ⋅ x → ∃℘ x ⋿ X 𝑠𝑡 y ⋿ g ⋅ x
          H (∃℘ x ,, x∈X ,, y⋿f[x]) = ∃℘ x ,, x∈X ,, (res[X]⸢⊑℘⸣ (res[f]⸢⊑↗⸣ f⊑g) y⋿f[x])

left-unit[*] : ∀ {ℓ} {A : Poset ℓ} {X : ⟪ ℘ A ⟫} → return♮ *♮ ⋅ X ≈♮ X
left-unit[*] {X = X} = ext⸢≈℘⸣ $ LHS , RHS 
  where
    LHS : ∀ {y} → y ⋿ return♮ *♮ ⋅ X → y ⋿ X
    LHS (∃℘ y' ,, y'∈X ,, y∈return[y']) = res[x]⸢⊑℘⸣ {X = X} y∈return[y'] y'∈X
    RHS : ∀ {y} → y ⋿ X → y ⋿ return♮ *♮ ⋅ X
    RHS {y} y∈X = ∃℘ y ,, y∈X ,, xRx

left-unit[*/ext] : ∀ {ℓ} {A : Poset ℓ} → return♮ {A = A} *♮ ≈♮ id♮
left-unit[*/ext] = ext⸢≈↗⸣ left-unit[*]

right-unit[*] : ∀ {ℓ} {A B : Poset ℓ} {f : ⟪ A ↗ ℘ B ⟫} {x : ⟪ A ⟫} → f *♮ ⋅ (return♮ ⋅ x) ≈♮ f ⋅ x
right-unit[*] {f = f} {x} = ext⸢≈℘⸣ $ LHS , RHS
  where
    LHS : ∀ {y} → y ⋿ f *♮ ⋅ (return♮ ⋅ x) → y ⋿ f ⋅ x
    LHS (∃℘ x' ,, x'∈return[x] ,, y∈f[x']) = res[X]⸢⊑℘⸣ (res[x]⸢⊑↗⸣ {f = f} x'∈return[x]) y∈f[x']
    RHS : ∀ {y} → y ⋿ f ⋅ x → y ⋿ f *♮ ⋅ (return♮ ⋅ x)
    RHS {y} y∈f[x] = ∃℘ x ,, xRx ,, y∈f[x]
    
associative[*] : ∀ {ℓ} {A B C : Poset ℓ} {g : ⟪ B ↗ ℘ C ⟫} {f : ⟪ A ↗ ℘ B ⟫} {X : ⟪ ℘ A ⟫} → (g *♮ ∘♮ f) *♮ ⋅ X ≈♮ g *♮ ⋅ (f *♮ ⋅ X)
associative[*] {g = g} {f} {X} = ext⸢≈℘⸣ $ LHS , RHS
  where
    LHS : ∀ {y} → y ⋿ (g *♮ ∘♮ f) *♮ ⋅ X → y ⋿ g *♮ ⋅ (f *♮ ⋅ X)
    LHS {y} (∃℘ x ,, x∈X ,, (∃℘ y' ,, y'∈f[x] ,, y∈g[y'])) = ∃℘ y' ,, (∃℘ x ,, x∈X ,, y'∈f[x]) ,, y∈g[y']
    RHS : ∀ {y} → y ⋿ g *♮ ⋅ (f *♮ ⋅ X) → y ⋿ (g *♮ ∘♮ f) *♮ ⋅ X
    RHS {y} (∃℘ y' ,, (∃℘ x ,, x∈X ,, y'∈f[x]) ,, y∈g[y']) = ∃℘ x ,, x∈X ,, ∃℘ y' ,, y'∈f[x] ,, y∈g[y']

associative[*/ext] : ∀ {ℓ} {A B C : Poset ℓ} {g : ⟪ B ↗ ℘ C ⟫} {f : ⟪ A ↗ ℘ B ⟫} → (g *♮ ∘♮ f) *♮ ≈♮ g *♮ ∘♮ f *♮
associative[*/ext] = ext⸢≈↗⸣ associative[*]

sound[*]⸢⊑⸣ : ∀ {ℓ} {A B : Poset ℓ} {f₁ f₂ : ⟪ A ↗ ℘ B ⟫} → f₁ ⊑♮ f₂ → f₁ *♮ ⊑♮ f₂ *♮
sound[*]⸢⊑⸣ {f₁ = f₁} {f₂} f₁⊑f₂ = let open ProofMode[⊑] in [proof-mode]
  do [[ f₁ *♮ ]]
   ‣ [focus-in [*] ] ⟅ f₁⊑f₂ ⟆
   ‣ [[ f₂ *♮ ]]
   ∎

sound[*]⸢≈⸣ : ∀ {ℓ} {A B : Poset ℓ} {f₁ f₂ : ⟪ A ↗ ℘ B ⟫} → f₁ ≈♮ f₂ → f₁ *♮ ≈♮ f₂ *♮
sound[*]⸢≈⸣ f₁≈f₂ = ⋈[] (sound[*]⸢⊑⸣ $ xRx[] f₁≈f₂) (sound[*]⸢⊑⸣ $ xRx[] $ ◇ f₁≈f₂)

complete[*]⸢⊑⸣ : ∀ {ℓ} {A B : Poset ℓ} {f₁ f₂ : ⟪ A ↗ ℘ B ⟫} → f₁ *♮ ⊑♮ f₂ *♮ → f₁ ⊑♮ f₂ 
complete[*]⸢⊑⸣ {f₁ = f₁} {f₂} f₁*⊑f₂* = let open ProofMode[⊑] in ext⸢⊑↗⸣ $ λ {x} → [proof-mode]
  do [[ f₁ ⋅ x ]]
   ‣ ⟅ ◇ right-unit[*] ⟆⸢≈⸣
   ‣ [[ f₁ *♮ ⋅ (return♮ ⋅ x) ]]
   ‣ [focus-left [⋅] 𝑜𝑓 return♮ ⋅ x ] ⟅ f₁*⊑f₂* ⟆
   ‣ [[ f₂ *♮ ⋅ (return♮ ⋅ x) ]]
   ‣ ⟅ right-unit[*] ⟆⸢≈⸣
   ‣ [[ f₂ ⋅ x ]]
   ∎

complete[*]⸢≈⸣ : ∀ {ℓ} {A B : Poset ℓ} {f₁ f₂ : ⟪ A ↗ ℘ B ⟫} → f₁ *♮ ≈♮ f₂ *♮ → f₁ ≈♮ f₂
complete[*]⸢≈⸣ f₁*≈f₂* = ⋈[] (complete[*]⸢⊑⸣ $ xRx[] f₁*≈f₂*) (complete[*]⸢⊑⸣ $ xRx[] $ ◇ f₁*≈f₂*)

[⟐] : ∀ {ℓ} {A B C : Poset ℓ} → ⟪ (B ↗ ℘ C) ↗ (A ↗ ℘ B) ↗ (A ↗ ℘ C) ⟫ 
[⟐] = [∘♮] ∘♮ [*]
  
_⟐_ : ∀ {ℓ} {A B C : Poset ℓ} → ⟪ B ↗ ℘ C ⟫ → ⟪ A ↗ ℘ B ⟫ → ⟪ A ↗ ℘ C ⟫
g ⟐ f = g *♮ ∘♮ f
  
left-unit[⟐] : ∀ {ℓ} {A B : Poset ℓ} {f : ⟪ A ↗ ℘ B ⟫} → return♮ ⟐ f ≈♮ f
left-unit[⟐] = ext⸢≈↗⸣ $ left-unit[*]
  
right-unit[⟐] : ∀ {ℓ} {A B : Poset ℓ} {f : ⟪ A ↗ ℘ B ⟫} → f ⟐ return♮ ≈♮ f
right-unit[⟐] = ext⸢≈↗⸣ right-unit[*]

right-unit[⟐/pure] : ∀ {ℓ} {A B C : Poset ℓ} {g : ⟪ B ↗ ℘ C ⟫} {f : ⟪ A ↗ B ⟫} → g ⟐ pure ⋅ f ≈♮ g ∘♮ f
right-unit[⟐/pure] {g = g} {f} = let open ProofMode[≈] in [proof-mode]
  do [[ g *♮ ∘♮ (pure ⋅ f) ]]
   ‣ ⟅ ◇ associative[∘♮] ⟆
   ‣ [[ (g *♮ ∘♮ return♮) ∘♮ f ]]
   ‣ [focus-left [∘♮] 𝑜𝑓 f ] begin 
       do [[ g *♮ ∘♮ return♮ ]]
        ‣ ⟅ right-unit[⟐] ⟆
        ‣ [[ g ]]
       end
   ‣ [[ g ∘♮ f ]]
   ∎

  
associative[⟐] : ∀ {ℓ} {A B C D : Poset ℓ} {h : ⟪ C ↗ ℘ D ⟫} {g : ⟪ B ↗ ℘ C ⟫} {f : ⟪ A ↗ ℘ B ⟫} → (h ⟐ g) ⟐ f ≈♮ h ⟐ (g ⟐ f)
associative[⟐] {h = h} {g} {f} = let open ProofMode[≈] in [proof-mode]
  do [[ (h ⟐ g) ⟐ f ]]
   ‣ [[ (h *♮ ∘♮ g) *♮ ∘♮ f ]]
   ‣ [focus-left [∘♮] 𝑜𝑓 f ] ⟅ associative[*/ext] ⟆
   ‣ [[ (h *♮ ∘♮ g *♮) ∘♮ f ]]
   ‣ ⟅ associative[∘♮] ⟆
   ‣ [[ h *♮ ∘♮ g *♮ ∘♮ f ]]
   ‣ [[ h ⟐ g ⟐ f ]]
   ∎

homomorphic[pure/⟐] : ∀ {ℓ} {A B C : Poset ℓ} {g : ⟪ B ↗ C ⟫} {f : ⟪ A ↗ B ⟫} → pure ⋅ g ⟐ pure ⋅ f ≈♮ pure ⋅ (g ∘♮ f)
homomorphic[pure/⟐] {g = g} {f} = let open ProofMode[≈] in [proof-mode]
  do [[ pure ⋅ g ⟐ pure ⋅ f ]]
   ‣ [[ (pure ⋅ g) *♮ ∘♮ pure ⋅ f ]]
   ‣ ⟅ right-unit[⟐/pure] ⟆
   ‣ [[ pure ⋅ g ∘♮ f ]]
   ‣ ⟅ ◇ homomorphic[pure/ext] ⟆
   ‣ [[ pure ⋅ (g ∘♮ f) ]]
   ∎

wrap[⟐] : ∀ {ℓ} {A B C D : Poset ℓ} → ⟪ (C ↗ ℘ D) ↗ (A ↗ ℘ B) ↗ (B ↗ ℘ C) ↗ A ↗ ℘ D ⟫
wrap[⟐] {A = A} {B} {C} {D} = witness (curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ C ↗ ℘ D ⟫ → ⟪ A ↗ ℘ B ⟫ → ⟪ B ↗ ℘ C ⟫ → ⟪ A ↗ ℘ D ⟫
    fun h f g = h ⟐ g ⟐ f
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_) fun
      ppr h₁⊑h₂ f₁⊑f₂ g₁⊑g₂ = ext⸢⊑↗⸣ $ λ {x} → res[fx]⸢⊑↗⸣ (sound[*]⸢⊑⸣ h₁⊑h₂) (res[fx]⸢⊑↗⸣ (sound[*]⸢⊑⸣ g₁⊑g₂) (res[f]⸢⊑↗⸣ f₁⊑f₂))
