module OSet.Lib where

open import Prelude
open import OSet.OSet
open import OSet.Fun
open import OSet.Power
open import OSet.Product
open import OSet.Classes
open import OSet.ProofMode

[⋅] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ (A ⇒ B) ⇒ A ⇒ B ⟫
[⋅] {A = A} {B} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⇒ B ⟫ → ⟪ A ⟫ → ⟪ B ⟫
    fun = _⋅_
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr f⊑g x⊑y = res-f-x[λ]⸢⊑⸣ f⊑g x⊑y

[⊙] : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} → ⟪ (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C) ⟫
[⊙] {A = A} {B} {C} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ B ⇒ C ⟫ → ⟪ A ⇒ B ⟫ → ⟪ A ⇒ C ⟫
    fun g f = g ⊙ f
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr {g₁} {g₂} g₁⊑g₂ {f₁} {f₂} f₁⊑f₂ = ext[λ]⸢⊑⸣ (res-f-x[λ]⸢⊑⸣ g₁⊑g₂ (res-f[λ]⸢⊑⸣ f₁⊑f₂))

associative[⊙] : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} {D : POSet 𝓁₄} {h : ⟪ C ⇒ D ⟫} {g : ⟪ B ⇒ C ⟫} {f : ⟪ A ⇒ B ⟫} → (h ⊙ g) ⊙ f ≈ h ⊙ (g ⊙ f)
associative[⊙] = ext[λ]⸢≈⸣ xRx⸢≈⸣

return : ∀ {𝓁} {A : POSet 𝓁} → ⟪ A ⇒ 𝒫 A ⟫
return {𝓁} {A} = witness-x (curry⸢λ⸣ id⸢ω⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ A ⟫ → Set 𝓁
    fun x y = y ⊑ x
    abstract
      ppr : proper (_⊑_ ⇉ _⊒_ ⇉ [→]) fun
      ppr x₁⊑x₂ y₁⊒y₂ x₁∈X₁ = x₁⊑x₂ ⌾ x₁∈X₁ ⌾ y₁⊒y₂

return↔⋿ : ∀ {𝓁} {A : POSet 𝓁} {x : ⟪ A ⟫} {X : ⟪ 𝒫 A ⟫} → return ⋅ x ⊑ X ↔ x ⋿ X
return↔⋿ {x = x} {X} =  (λ return[x]⊑X → res-X[ω]⸢⊑⸣ return[x]⊑X xRx) , (λ x∈X → ext[ω]⸢⊑⸣ (λ x⊒y → res-x[ω]⸢⊑⸣ {X = X} x⊒y x∈X))

ext[⋿][⊑]⸢return⸣ : ∀ {𝓁} {A : POSet 𝓁} {X Y : ⟪ 𝒫 A ⟫} → (∀ {x} → return ⋅ x ⊑ X → return ⋅ x ⊑ Y) → X ⊑ Y
ext[⋿][⊑]⸢return⸣ X⊑Y = ext[ω]⸢⊑⸣ $ π₁ return↔⋿ ∘ X⊑Y ∘ π₂ return↔⋿

ext[⋿][≈]⸢return⸣ : ∀ {𝓁} {A : POSet 𝓁} {X Y : ⟪ 𝒫 A ⟫} → (∀ {x} → return ⋅ x ⊑ X ↔ return ⋅ x ⊑ Y) → X ≈ Y
ext[⋿][≈]⸢return⸣ {X = X} {Y} X≈Y = ext[ω]⸢≈⸣ $ π₁ return↔⋿ ∘ π₁ X≈Y ∘ π₂ return↔⋿ , π₁ return↔⋿ ∘ π₂ X≈Y ∘ π₂ return↔⋿

pure : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ (A ⇒ B) ⇒ (A ⇒ 𝒫 B) ⟫
pure = [⊙] ⋅ return

injective[pure]⸢⊑⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f g : ⟪ A ⇒ B ⟫} → pure ⋅ f ⊑ pure ⋅ g → f ⊑ g
injective[pure]⸢⊑⸣ pure[f]⊑pure[g] = ext[λ]⸢⊑⸣ $ π₁ return↔⋿ (res-f[λ]⸢⊑⸣ pure[f]⊑pure[g])
  
associative[pure]⸢⊙⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ C ⟫} {f : ⟪ A ⇒ B ⟫} → pure ⋅ g ⊙ f ≈ pure ⋅ (g ⊙ f)
associative[pure]⸢⊙⸣ = associative[⊙]

associative[pure] : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ C ⟫} {f : ⟪ A ⇒ B ⟫} {x : ⟪ A ⟫} → pure ⋅ g ⋅ (f ⋅ x) ≈ pure ⋅ (g ⊙ f) ⋅ x
associative[pure] {g = g} {f} {x} = res-f[λ]⸢≈⸣ {x = x} $ associative[pure]⸢⊙⸣ {g = g} {f}

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
      ppr X⊑Y x⊒y (∃𝒫 z ,, z∈X ,, x∈f[z]) = ∃𝒫 z ,, res-X[ω]⸢⊑⸣ X⊑Y z∈X ,, res-x[ω]⸢⊑⸣ {X = f ⋅ z} x⊒y x∈f[z]

[*] : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ (A ⇒ 𝒫 B) ⇒ (𝒫 A ⇒ 𝒫 B) ⟫
[*] {𝓁} {A} {B} = witness-x (curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⇒ 𝒫 B ⟫ → ⟪ 𝒫 A ⇒ 𝒫 B ⟫
    fun f = f *
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_) fun
      ppr {f} {g} f⊑g = ext[λ]⸢⊑⸣ $ ext[ω]⸢⊑⸣ H
        where
          H : ∀ {X y} → ∃𝒫 x ⋿ X 𝑠𝑡 y ⋿ f ⋅ x → ∃𝒫 x ⋿ X 𝑠𝑡 y ⋿ g ⋅ x
          H (∃𝒫 x ,, x∈X ,, y⋿f[x]) = ∃𝒫 x ,, x∈X ,, (res-X[ω]⸢⊑⸣ (res-f[λ]⸢⊑⸣ f⊑g) y⋿f[x])


left-unit[*] : ∀ {𝓁} {A : POSet 𝓁} {X : ⟪ 𝒫 A ⟫} → return * ⋅ X ≈ X
left-unit[*] {X = X} = ext[ω]⸢≈⸣ $ LHS , RHS 
  where
    LHS : ∀ {y} → y ⋿ return * ⋅ X → y ⋿ X
    LHS (∃𝒫 y' ,, y'∈X ,, y∈return[y']) = res-x[ω]⸢⊑⸣ {X = X} y∈return[y'] y'∈X
    RHS : ∀ {y} → y ⋿ X → y ⋿ return * ⋅ X
    RHS {y} y∈X = ∃𝒫 y ,, y∈X ,, xRx

left-unit[*]⸢⊙⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f : ⟪ A ⇒ 𝒫 B ⟫} → return * ⊙ f ≈ f
left-unit[*]⸢⊙⸣ = ext[λ]⸢≈⸣ $ left-unit[*]

left-unit[*]⸢id⸣ : ∀ {𝓁} {A : POSet 𝓁} → return {A = A} * ≈ ↑id
left-unit[*]⸢id⸣ = ext[λ]⸢≈⸣ left-unit[*]

right-unit[*] : ∀ {𝓁} {A B : POSet 𝓁} {f : ⟪ A ⇒ 𝒫 B ⟫} {x : ⟪ A ⟫} → f * ⋅ (return ⋅ x) ≈ f ⋅ x
right-unit[*] {f = f} {x} = ext[ω]⸢≈⸣ $ LHS , RHS
  where
    LHS : ∀ {y} → y ⋿ f * ⋅ (return ⋅ x) → y ⋿ f ⋅ x
    LHS (∃𝒫 x' ,, x'∈return[x] ,, y∈f[x']) = res-X[ω]⸢⊑⸣ (res-x[λ]⸢⊑⸣ {f = f} x'∈return[x]) y∈f[x']
    RHS : ∀ {y} → y ⋿ f ⋅ x → y ⋿ f * ⋅ (return ⋅ x)
    RHS {y} y∈f[x] = ∃𝒫 x ,, xRx ,, y∈f[x]
    
right-unit[*]⸢⊙⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f : ⟪ A ⇒ 𝒫 B ⟫} → f * ⊙ return ≈ f
right-unit[*]⸢⊙⸣ = ext[λ]⸢≈⸣ right-unit[*]

right-unit[*]⸢pure⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ B ⟫} → g * ⊙ (pure ⋅ f) ≈ g ⊙ f 
right-unit[*]⸢pure⸣ {g = g} {f} = [≈-proof-mode]
  do [≈][[ g * ⊙ (pure ⋅ f) ]]
  ≈‣ [≈] (g * ⊙ return) ⊙ f   ⟅ ◇ associative[⊙] ⟆
  ≈‣ [≈-focus-left [⊙] 𝑜𝑓 f ] [≈] g ⟅ right-unit[*]⸢⊙⸣ ⟆
  ≈‣ [≈][[ g ⊙ f ]]
  ⬜

associative[*] : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ 𝒫 B ⟫} {X : ⟪ 𝒫 A ⟫} → (g * ⊙ f) * ⋅ X ≈ g * ⋅ (f * ⋅ X)
associative[*] {g = g} {f} {X} = ext[ω]⸢≈⸣ $ LHS , RHS
  where
    LHS : ∀ {y} → y ⋿ (g * ⊙ f) * ⋅ X → y ⋿ g * ⋅ (f * ⋅ X)
    LHS {y} (∃𝒫 x ,, x∈X ,, (∃𝒫 y' ,, y'∈f[x] ,, y∈g[y'])) = ∃𝒫 y' ,, (∃𝒫 x ,, x∈X ,, y'∈f[x]) ,, y∈g[y']
    RHS : ∀ {y} → y ⋿ g * ⋅ (f * ⋅ X) → y ⋿ (g * ⊙ f) * ⋅ X
    RHS {y} (∃𝒫 y' ,, (∃𝒫 x ,, x∈X ,, y'∈f[x]) ,, y∈g[y']) = ∃𝒫 x ,, x∈X ,, ∃𝒫 y' ,, y'∈f[x] ,, y∈g[y']

associative[*]⸢⊙⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ 𝒫 B ⟫} → (g * ⊙ f) * ≈ g * ⊙ f *
associative[*]⸢⊙⸣ = ext[λ]⸢≈⸣ associative[*]

right-unit[*]⸢X⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ B ⟫} {X : ⟪ 𝒫 A ⟫} → g * ⋅ ((pure ⋅ f) * ⋅ X) ≈ (g ⊙ f) * ⋅ X
right-unit[*]⸢X⸣ {g = g} {f} {X} = [≈-proof-mode]
  do [≈][[ g * ⋅ ((pure ⋅ f) * ⋅ X) ]]
  ≈‣ [≈-≡] (g * ⊙ (pure ⋅ f) *) ⋅ X ⟅ ↯ ⟆
  ≈‣ [≈] (g * ⊙ pure ⋅ f) * ⋅ X ⟅ ◇ associative[*] ⟆
  ≈‣ [≈-focus-left [⋅] 𝑜𝑓 X ] $
     [≈-focus-in [*] ] [≈] g ⊙ f ⟅ right-unit[*]⸢pure⸣ ⟆
  ≈‣ [≈][[ (g ⊙ f) * ⋅ X ]]
  ⬜

right-unit[*]⸢X⸣⸢⊙⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ B ⟫} → g * ⊙ (pure ⋅ f) * ≈ (g ⊙ f) *
right-unit[*]⸢X⸣⸢⊙⸣ = ext[λ]⸢≈⸣ right-unit[*]⸢X⸣

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
associative[⟐] {h = h} {g} {f} = [≈-proof-mode]
  do [≈][[ (h ⟐ g) ⟐ f ]]
  ≈‣ [≈-≡] (h * ⊙ g) * ⊙ f ⟅ ↯ ⟆
  ≈‣ [≈-focus-left [⊙] 𝑜𝑓 f ] [≈] h * ⊙ g * ⟅ associative[*]⸢⊙⸣ ⟆
  ≈‣ [≈][[ (h * ⊙ g *) ⊙ f ]]
  ≈‣ [≈] h * ⊙ g * ⊙ f ⟅ associative[⊙] ⟆
  ≈‣ [≈-≡] h ⟐ g ⟐ f ⟅ ↯ ⟆
  ⬜

associative[⟐]⸢*⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ 𝒫 B ⟫} {X : ⟪ 𝒫 A ⟫} → (g ⟐ f) * ⋅ X ≈ g * ⋅ (f * ⋅ X)
associative[⟐]⸢*⸣ = associative[*]

associative[⟐]⸢⊙⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ 𝒫 C ⟫} {f : ⟪ A ⇒ 𝒫 B ⟫} → (g ⟐ f) * ≈ g * ⊙ f *
associative[⟐]⸢⊙⸣ = associative[*]⸢⊙⸣
  
homomorphic[⟐]⸢pure⸣ : ∀ {𝓁} {A B C : POSet 𝓁} {g : ⟪ B ⇒ C ⟫} {f : ⟪ A ⇒ B ⟫} → pure ⋅ g ⟐ pure ⋅ f ≈ pure ⋅ (g ⊙ f)
homomorphic[⟐]⸢pure⸣ {g = g} {f} = [≈-proof-mode]
  do [≈][[ pure ⋅ g ⟐ pure ⋅ f ]]
  ≈‣ [≈-≡] (pure ⋅ g) * ⊙ pure ⋅ f ⟅ ↯ ⟆
  ≈‣ [≈] pure ⋅ g ⊙ f ⟅ right-unit[*]⸢pure⸣ ⟆
  ≈‣ [≈] pure ⋅ (g ⊙ f) ⟅ associative[pure]⸢⊙⸣ ⟆
  ⬜

injective[*]⸢⊑-ext⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f g : ⟪ A ⇒ 𝒫 B ⟫} → f * ⊑ g * → ∀ {x y} → y ⋿ f ⋅ x → y ⋿ g ⋅ x
injective[*]⸢⊑-ext⸣ {f = f} {g} f*⊑g* {x} {y} y∈f[x] with res-X[ω]⸢⊑⸣ (res-f[λ]⸢⊑⸣ {x = return ⋅ x} f*⊑g*) (∃𝒫 x ,, xRx ,, y∈f[x])
... | ∃𝒫 x' ,, x'⊑x ,, y∈g[x'] = res-X[ω]⸢⊑⸣ (res-x[λ]⸢⊑⸣ {f = g} x'⊑x) y∈g[x']

injective[*]⸢⊑⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f g : ⟪ A ⇒ 𝒫 B ⟫} → f * ⊑ g * → f ⊑ g
injective[*]⸢⊑⸣ f*⊑g* = ext[λ]⸢⊑⸣ $ λ {x} → ext[ω]⸢⊑⸣ $ λ {y} → injective[*]⸢⊑-ext⸣ f*⊑g* {x = x} {y}

injective[*]⸢≈⸣ : ∀ {𝓁} {A B : POSet 𝓁} {f g : ⟪ A ⇒ 𝒫 B ⟫} → f * ≈ g * → f ≈ g
injective[*]⸢≈⸣ f*≈g* = ⋈[] (injective[*]⸢⊑⸣ $ xRx[] f*≈g*) (injective[*]⸢⊑⸣ $ xRx[] $ ◇ f*≈g*)

all : ∀ {𝓁} (A : POSet 𝓁) → ⟪ 𝒫 A ⟫
all {𝓁} A = witness-x id⸢ω⸣ $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → Set 𝓁
    fun = const $ lifted 𝓁 unit
    abstract
      ppr : proper (_⊒_ {A = ⟪ A ⟫} ⇉ [→]) fun
      ppr = const id

all-in : ∀ {𝓁} {A : POSet 𝓁} {x : ⟪ A ⟫} → x ⋿ all A
all-in = Lift tt

↑const : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ A ⇒ B ⇒ A ⟫
↑const {A = A} {B} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ B ⟫ → ⟪ A ⟫
    fun = const
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr x⊑y _ = x⊑y

↑uncurry : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} → ⟪ (A ⇒ B ⇒ C) ⇒ A ⟨×⟩ B ⇒ C ⟫
↑uncurry {A = A} {B} {C} = witness-x (curry⸢λ⸣ $ curry⸢λ↑⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⇒ B ⇒ C ⟫ → prod A B → ⟪ C ⟫
    fun f (x , y) = f ⋅ x ⋅ y
    abstract
      ppr : proper (_⊑_ ⇉ _⊴_ ⇉ _⊑_) fun
      ppr f⊑g (x₁⊑x₂ , y₁⊑y₂) = res-f-x[λ]⸢⊑⸣ (res-f-x[λ]⸢⊑⸣ f⊑g x₁⊑x₂) y₁⊑y₂

↑split : ∀ {𝓁} {A : POSet 𝓁} → ⟪ A ⇒ A ⟨×⟩ A ⟫
↑split {A = A} = witness-x (curry⸢λ⸣ id⸢λ↑⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → prod A A
    fun x = x , x
    abstract
      ppr : proper (_⊑_ ⇉ _⊴_) fun
      ppr x⊑y = x⊑y , x⊑y

↑apply⸢×⸣ : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} {D : POSet 𝓁₄} → ⟪ (A ⇒ B) ⟨×⟩ (C ⇒ D) ⇒ A ⟨×⟩ C ⇒ B ⟨×⟩ D ⟫
↑apply⸢×⸣ {𝓁₁} {𝓁₂} {𝓁₃} {𝓁₄} {A} {B} {C} {D} = witness-x (curry⸢λ↑⸣ $ curry⸢λ↑⸣ {𝓁₂ʳ = 𝓁₂ ⊔ˡ 𝓁₄} id⸢λ↑⸣) $ mk[witness] fun ppr
  where
    fun : prod (A ⇒ B) (C ⇒ D) → prod A C → prod B D
    fun (f , g) (x , y) = f ⋅ x , g ⋅ y
    abstract
      ppr : proper (_⊴_ ⇉ _⊴_ ⇉ _⊴_) fun
      ppr (f₁⊑f₂ , g₁⊑g₂) (x₁⊑x₂ , y₁⊑y₂) = res-f-x[λ]⸢⊑⸣ f₁⊑f₂ x₁⊑x₂ , res-f-x[λ]⸢⊑⸣ g₁⊑g₂ y₁⊑y₂
  
↑empty : ∀ {𝓁} {A : POSet 𝓁} → ⟪ 𝒫 A ⟫
↑empty {𝓁} {A} = witness-x id⸢ω⸣ $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → Set 𝓁
    fun = const $ lifted 𝓁 void
    abstract
      ppr : proper (_⊑_ ⇉ [→]) fun
      ppr _ (Lift ())

↑π₁ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ A ⟨×⟩ B ⇒ A ⟫
↑π₁ {A = A} {B} = witness-x (curry⸢λ↑⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : prod A B → ⟪ A ⟫
    fun (x , y) = x
    abstract
      ppr : proper (_⊴_ ⇉ _⊑_) fun
      ppr (x₁⊑x₂ , y₁⊑y₂) = x₁⊑x₂

↑π₂ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ A ⟨×⟩ B ⇒ B ⟫
↑π₂ {A = A} {B} = witness-x (curry⸢λ↑⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : prod A B → ⟪ B ⟫
    fun (x , y) = y
    abstract
      ppr : proper (_⊴_ ⇉ _⊑_) fun
      ppr (x₁⊑x₂ , y₁⊑y₂) = y₁⊑y₂
