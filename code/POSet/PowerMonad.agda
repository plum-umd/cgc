module POSet.PowerMonad where

open import Prelude
open import POSet.POSet
open import POSet.Fun
open import POSet.Power
open import POSet.ProofMode
open import POSet.Lib

return : ∀ {𝓁} {A : POSet 𝓁} → ⟪ A ⇒ 𝒫 A ⟫
return {𝓁} {A} = witness-x (curry⸢λ⸣ id⸢ω⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ A ⟫ → Set 𝓁
    fun x y = y ⊑ x
    abstract
      ppr : proper (_⊑_ ⇉ _⊒_ ⇉ [→]) fun
      ppr x₁⊑x₂ y₁⊒y₂ x₁∈X₁ = x₁⊑x₂ ⌾ x₁∈X₁ ⌾ y₁⊒y₂

return↔⋿ : ∀ {𝓁} {A : POSet 𝓁} {x : ⟪ A ⟫} {X : ⟪ 𝒫 A ⟫} → return ⋅ x ⊑ X ↔ x ⋿ X
return↔⋿ {x = x} {X} =  (λ return[x]⊑X → res-X[𝒫]⸢⊑⸣ return[x]⊑X xRx) , (λ x∈X → ext[𝒫]⸢⊑⸣ (λ x⊒y → res-x[𝒫]⸢⊑⸣ {X = X} x⊒y x∈X))

ext[𝒫][return]⸢⊑⸣ : ∀ {𝓁} {A : POSet 𝓁} {X Y : ⟪ 𝒫 A ⟫} → (∀ {x} → return ⋅ x ⊑ X → return ⋅ x ⊑ Y) → X ⊑ Y
ext[𝒫][return]⸢⊑⸣ X⊑Y = ext[𝒫]⸢⊑⸣ $ π₁ return↔⋿ ∘ X⊑Y ∘ π₂ return↔⋿

ext[⋿][return]⸢≈⸣ : ∀ {𝓁} {A : POSet 𝓁} {X Y : ⟪ 𝒫 A ⟫} → (∀ {x} → return ⋅ x ⊑ X ↔ return ⋅ x ⊑ Y) → X ≈ Y
ext[⋿][return]⸢≈⸣ {X = X} {Y} X≈Y = ext[𝒫]⸢≈⸣ $ π₁ return↔⋿ ∘ π₁ X≈Y ∘ π₂ return↔⋿ , π₁ return↔⋿ ∘ π₂ X≈Y ∘ π₂ return↔⋿

pure : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ (A ⇒ B) ⇒ (A ⇒ 𝒫 B) ⟫
pure = [⊙] ⋅ return

injective[pure]⸢⊑⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f g : ⟪ A ⇒ B ⟫} → pure ⋅ f ⊑ pure ⋅ g → f ⊑ g
injective[pure]⸢⊑⸣ pure[f]⊑pure[g] = ext[⇒]⸢⊑⸣ $ π₁ return↔⋿ (res-f[⇒]⸢⊑⸣ pure[f]⊑pure[g])
  
homomorphic[pure]⸢⊙⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ C ⟫} {f : ⟪ A ⇒ B ⟫} → pure ⋅ (g ⊙ f) ≈ pure ⋅ g ⊙ f
homomorphic[pure]⸢⊙⸣ = ◇ associative[⊙]

homomorphic[pure] : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ C ⟫} {f : ⟪ A ⇒ B ⟫} {x : ⟪ A ⟫} → pure ⋅ (g ⊙ f) ⋅ x ≈ pure ⋅ g ⋅ (f ⋅ x)
homomorphic[pure] {g = g} {f} = res-f[⇒]⸢≈⸣ $ homomorphic[pure]⸢⊙⸣ {g = g} {f}

syntax Σ𝒫 X (λ x → P) = ∃𝒫 x ⋿ X 𝑠𝑡 P
infixr 2 Σ𝒫
infixr 2 ∃𝒫_,,_,,_
record Σ𝒫 {𝓁} {A : POSet 𝓁} (X : ⟪ 𝒫 A ⟫) (P : ⟪ A ⟫ → Set 𝓁) : Set 𝓁 where
  constructor ∃𝒫_,,_,,_
  field
    x : ⟪ A ⟫
    x∈X : x ⋿ X
    P[x] : P x
      
_* : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ A ⇒ 𝒫 B ⟫ → ⟪ 𝒫 A ⇒ 𝒫 B ⟫
_* {𝓁} {A} {B} f = witness-x (curry⸢λ⸣ id⸢ω⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ 𝒫 A ⟫ → ⟪ B ⟫ → Set 𝓁
    fun X y = Σ𝒫 X (λ x → y ⋿ f ⋅ x)
    abstract
      ppr : proper (_⊑_ ⇉ _⊒_ ⇉ [→]) fun
      ppr X⊑Y x⊒y (∃𝒫 z ,, z∈X ,, x∈f[z]) = ∃𝒫 z ,, res-X[𝒫]⸢⊑⸣ X⊑Y z∈X ,, res-x[𝒫]⸢⊑⸣ {X = f ⋅ z} x⊒y x∈f[z]

[*] : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ (A ⇒ 𝒫 B) ⇒ (𝒫 A ⇒ 𝒫 B) ⟫
[*] {𝓁} {A} {B} = witness-x (curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⇒ 𝒫 B ⟫ → ⟪ 𝒫 A ⇒ 𝒫 B ⟫
    fun f = f *
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_) fun
      ppr {f} {g} f⊑g = ext[⇒]⸢⊑⸣ $ ext[𝒫]⸢⊑⸣ H
        where
          H : ∀ {X y} → ∃𝒫 x ⋿ X 𝑠𝑡 y ⋿ f ⋅ x → ∃𝒫 x ⋿ X 𝑠𝑡 y ⋿ g ⋅ x
          H (∃𝒫 x ,, x∈X ,, y⋿f[x]) = ∃𝒫 x ,, x∈X ,, (res-X[𝒫]⸢⊑⸣ (res-f[⇒]⸢⊑⸣ f⊑g) y⋿f[x])

left-unit[*] : ∀ {𝓁} {A : POSet 𝓁} {X : ⟪ 𝒫 A ⟫} → return * ⋅ X ≈ X
left-unit[*] {X = X} = ext[𝒫]⸢≈⸣ $ LHS , RHS 
  where
    LHS : ∀ {y} → y ⋿ return * ⋅ X → y ⋿ X
    LHS (∃𝒫 y' ,, y'∈X ,, y∈return[y']) = res-x[𝒫]⸢⊑⸣ {X = X} y∈return[y'] y'∈X
    RHS : ∀ {y} → y ⋿ X → y ⋿ return * ⋅ X
    RHS {y} y∈X = ∃𝒫 y ,, y∈X ,, xRx

left-unit[*]⸢⊙⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f : ⟪ A ⇒ 𝒫 B ⟫} → return * ⊙ f ≈ f
left-unit[*]⸢⊙⸣ = ext[⇒]⸢≈⸣ $ left-unit[*]

left-unit[*]⸢ext⸣ : ∀ {𝓁} {A : POSet 𝓁} → return {A = A} * ≈ id⁺
left-unit[*]⸢ext⸣ = ext[⇒]⸢≈⸣ left-unit[*]

right-unit[*] : ∀ {𝓁} {A B : POSet 𝓁} {f : ⟪ A ⇒ 𝒫 B ⟫} {x : ⟪ A ⟫} → f * ⋅ (return ⋅ x) ≈ f ⋅ x
right-unit[*] {f = f} {x} = ext[𝒫]⸢≈⸣ $ LHS , RHS
  where
    LHS : ∀ {y} → y ⋿ f * ⋅ (return ⋅ x) → y ⋿ f ⋅ x
    LHS (∃𝒫 x' ,, x'∈return[x] ,, y∈f[x']) = res-X[𝒫]⸢⊑⸣ (res-x[⇒]⸢⊑⸣ {f = f} x'∈return[x]) y∈f[x']
    RHS : ∀ {y} → y ⋿ f ⋅ x → y ⋿ f * ⋅ (return ⋅ x)
    RHS {y} y∈f[x] = ∃𝒫 x ,, xRx ,, y∈f[x]
    
right-unit[*]⸢⊙⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f : ⟪ A ⇒ 𝒫 B ⟫} → f * ⊙ return ≈ f
right-unit[*]⸢⊙⸣ = ext[⇒]⸢≈⸣ right-unit[*]

right-unit[*]⸢pure⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ B ⟫} → g * ⊙ (pure ⋅ f) ≈ g ⊙ f 
right-unit[*]⸢pure⸣ {g = g} {f} = let open §-ProofMode[≈] in [proof-mode]
  do [[ g * ⊙ (pure ⋅ f) ]]
   ‣ ⟅ ◇ associative[⊙] ⟆
   ‣ [[ (g * ⊙ return) ⊙ f ]]
   ‣ [focus-left [⊙] 𝑜𝑓 f ] begin 
       do [[ g * ⊙ return ]]
        ‣ ⟅ right-unit[*]⸢⊙⸣ ⟆
        ‣ [[ g ]]
       end
   ‣ [[ g ⊙ f ]]
   ∎

associative[*] : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ 𝒫 B ⟫} {X : ⟪ 𝒫 A ⟫} → (g * ⊙ f) * ⋅ X ≈ g * ⋅ (f * ⋅ X)
associative[*] {g = g} {f} {X} = ext[𝒫]⸢≈⸣ $ LHS , RHS
  where
    LHS : ∀ {y} → y ⋿ (g * ⊙ f) * ⋅ X → y ⋿ g * ⋅ (f * ⋅ X)
    LHS {y} (∃𝒫 x ,, x∈X ,, (∃𝒫 y' ,, y'∈f[x] ,, y∈g[y'])) = ∃𝒫 y' ,, (∃𝒫 x ,, x∈X ,, y'∈f[x]) ,, y∈g[y']
    RHS : ∀ {y} → y ⋿ g * ⋅ (f * ⋅ X) → y ⋿ (g * ⊙ f) * ⋅ X
    RHS {y} (∃𝒫 y' ,, (∃𝒫 x ,, x∈X ,, y'∈f[x]) ,, y∈g[y']) = ∃𝒫 x ,, x∈X ,, ∃𝒫 y' ,, y'∈f[x] ,, y∈g[y']

associative[*]⸢⊙⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ 𝒫 B ⟫} → (g * ⊙ f) * ≈ g * ⊙ f *
associative[*]⸢⊙⸣ = ext[⇒]⸢≈⸣ associative[*]

sound[*]⸢⊑⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f₁ f₂ : ⟪ A ⇒ 𝒫 B ⟫} → f₁ ⊑ f₂ → f₁ * ⊑ f₂ *
sound[*]⸢⊑⸣ {f₁ = f₁} {f₂} f₁⊑f₂ = let open §-ProofMode[⊑] in [proof-mode]
  do [[ f₁ * ]]
   ‣ [focus-in [*] ] ⟅ f₁⊑f₂ ⟆
   ‣ [[ f₂ * ]]
   ∎

sound[*]⸢≈⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f₁ f₂ : ⟪ A ⇒ 𝒫 B ⟫} → f₁ ≈ f₂ → f₁ * ≈ f₂ *
sound[*]⸢≈⸣ f₁≈f₂ = ⋈[] (sound[*]⸢⊑⸣ $ xRx[] f₁≈f₂) (sound[*]⸢⊑⸣ $ xRx[] $ ◇ f₁≈f₂)

complete[*]⸢⊑⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f₁ f₂ : ⟪ A ⇒ 𝒫 B ⟫} → f₁ * ⊑ f₂ * → f₁ ⊑ f₂ 
complete[*]⸢⊑⸣ {f₁ = f₁} {f₂} f₁*⊑f₂* = let open §-ProofMode[⊑] in ext[⇒]⸢⊑⸣ $ λ {x} → [proof-mode]
  do [[ f₁ ⋅ x ]]
   ‣ ⟅ ◇ right-unit[*] ⟆⸢≈⸣
   ‣ [[ f₁ * ⋅ (return ⋅ x) ]]
   ‣ [focus-left [⋅] 𝑜𝑓 return ⋅ x ] ⟅ f₁*⊑f₂* ⟆
   ‣ [[ f₂ * ⋅ (return ⋅ x) ]]
   ‣ ⟅ right-unit[*] ⟆⸢≈⸣
   ‣ [[ f₂ ⋅ x ]]
   ∎

complete[*]⸢≈⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f₁ f₂ : ⟪ A ⇒ 𝒫 B ⟫} → f₁ * ≈ f₂ * → f₁ ≈ f₂
complete[*]⸢≈⸣ f₁*≈f₂* = ⋈[] (complete[*]⸢⊑⸣ $ xRx[] f₁*≈f₂*) (complete[*]⸢⊑⸣ $ xRx[] $ ◇ f₁*≈f₂*)

[⟐] : ∀ {𝓁} {A B C : POSet 𝓁} → ⟪ (B ⇒ 𝒫 C) ⇒ (A ⇒ 𝒫 B) ⇒ (A ⇒ 𝒫 C) ⟫ 
[⟐] = [⊙] ⊙ [*]
  
infixr 9 _⟐_
_⟐_ : ∀ {𝓁} {A B C : POSet 𝓁} → ⟪ B ⇒ 𝒫 C ⟫ → ⟪ A ⇒ 𝒫 B ⟫ → ⟪ A ⇒ 𝒫 C ⟫
g ⟐ f = g * ⊙ f
  
left-unit[⟐] : ∀ {𝓁} {A B : POSet 𝓁} {f : ⟪ A ⇒ 𝒫 B ⟫} → return ⟐ f ≈ f
left-unit[⟐] = left-unit[*]⸢⊙⸣
  
right-unit[⟐] : ∀ {𝓁} {A B : POSet 𝓁} {f : ⟪ A ⇒ 𝒫 B ⟫} → f ⟐ return ≈ f
right-unit[⟐] = right-unit[*]⸢⊙⸣

right-unit[⟐]⸢pure⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ B ⟫} → g ⟐ pure ⋅ f ≈ g ⊙ f
right-unit[⟐]⸢pure⸣ = right-unit[*]⸢pure⸣
  
associative[⟐] : ∀ {𝓁} {A B C D : POSet 𝓁} {h : ⟪ C ⇒ 𝒫 D ⟫} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ 𝒫 B ⟫} → (h ⟐ g) ⟐ f ≈ h ⟐ (g ⟐ f)
associative[⟐] {h = h} {g} {f} = let open §-ProofMode[≈] in [proof-mode]
  do [[ (h ⟐ g) ⟐ f ]]
   ‣ [[ (h * ⊙ g) * ⊙ f ]]
   ‣ [focus-left [⊙] 𝑜𝑓 f ] ⟅ associative[*]⸢⊙⸣ ⟆
   ‣ [[ (h * ⊙ g *) ⊙ f ]]
   ‣ ⟅ associative[⊙] ⟆
   ‣ [[ h * ⊙ g * ⊙ f ]]
   ‣ [[ h ⟐ g ⟐ f ]]
   ∎

associative[⟐]⸢*⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ 𝒫 B ⟫} {X : ⟪ 𝒫 A ⟫} → (g ⟐ f) * ⋅ X ≈ g * ⋅ (f * ⋅ X)
associative[⟐]⸢*⸣ = associative[*]

associative[⟐]⸢⊙⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ 𝒫 B ⟫} → (g ⟐ f) * ≈ g * ⊙ f *
associative[⟐]⸢⊙⸣ = associative[*]⸢⊙⸣
  
homomorphic[pure]⸢⟐⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ C ⟫} {f : ⟪ A ⇒ B ⟫} → pure ⋅ g ⟐ pure ⋅ f ≈ pure ⋅ (g ⊙ f)
homomorphic[pure]⸢⟐⸣ {g = g} {f} = let open §-ProofMode[≈] in [proof-mode]
  do [[ pure ⋅ g ⟐ pure ⋅ f ]]
   ‣ [[ (pure ⋅ g) * ⊙ pure ⋅ f ]]
   ‣ ⟅ right-unit[*]⸢pure⸣ ⟆
   ‣ [[ pure ⋅ g ⊙ f ]]
   ‣ ⟅ ◇ homomorphic[pure]⸢⊙⸣ ⟆
   ‣ [[ pure ⋅ (g ⊙ f) ]]
   ∎

wrap[⟐] : ∀ {𝓁} {A B C D : POSet 𝓁} → ⟪ (C ⇒ 𝒫 D) ⇒ (A ⇒ 𝒫 B) ⇒ (B ⇒ 𝒫 C) ⇒ A ⇒ 𝒫 D ⟫
wrap[⟐] {A = A} {B} {C} {D} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ C ⇒ 𝒫 D ⟫ → ⟪ A ⇒ 𝒫 B ⟫ → ⟪ B ⇒ 𝒫 C ⟫ → ⟪ A ⇒ 𝒫 D ⟫
    fun h f g = h ⟐ g ⟐ f
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr h₁⊑h₂ f₁⊑f₂ g₁⊑g₂ = ext[⇒]⸢⊑⸣ $ λ {x} → res-f-x[⇒]⸢⊑⸣ (sound[*]⸢⊑⸣ h₁⊑h₂) (res-f-x[⇒]⸢⊑⸣ (sound[*]⸢⊑⸣ g₁⊑g₂) (res-f[⇒]⸢⊑⸣ f₁⊑f₂))
