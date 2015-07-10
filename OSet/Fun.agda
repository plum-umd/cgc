module OSet.Fun where

open import Prelude
open import OSet.OSet

data mon {𝓁₁ 𝓁₂} (A : POSet 𝓁₁) (B : POSet 𝓁₂) : Set (𝓁₁ ⊔ˡ 𝓁₂) where
  [λ_] : (f : ⟪ A ⟫  → ⟪ B ⟫) → {f-proper : proper (_⊑_ ⇉ _⊑_) f} → mon A B

data _⊴⸢mon⸣_ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} : relation (𝓁₁ ⊔ˡ 𝓁₂) (mon A B) where
  ↑⟨_⟩ :
    ∀ {f : ⟪ A ⟫ → ⟪ B ⟫} {f-proper : proper (_⊑_ ⇉ _⊑_) f} {g : ⟪ A ⟫ → ⟪ B ⟫} {g-proper : proper (_⊑_ ⇉ _⊑_) g}
    → (_⊑_ ⇉ _⊑_) f g → [λ f ] {f-proper} ⊴⸢mon⸣ [λ g ] {g-proper}

xRx⸢⊴⸢mon⸣⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → reflexive (_⊴⸢mon⸣_ {A = A} {B})
xRx⸢⊴⸢mon⸣⸣ {x = [λ f ] {f-proper}} = ↑⟨ f-proper ⟩

_⌾⸢⊴⸢mon⸣⸣_ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → transitive (_⊴⸢mon⸣_ {A = A} {B})
↑⟨ g⊑h ⟩ ⌾⸢⊴⸢mon⸣⸣ ↑⟨ f⊑g ⟩ = ↑⟨ (λ x⊑y → g⊑h xRx ⌾ f⊑g x⊑y) ⟩

instance
  Reflexive[mon] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Reflexive (_⊴⸢mon⸣_ {A = A} {B})
  Reflexive[mon] = record { xRx = xRx⸢⊴⸢mon⸣⸣ }
  Transitive[mon] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Transitive (_⊴⸢mon⸣_ {A = A} {B})
  Transitive[mon] = record { _⌾_ = _⌾⸢⊴⸢mon⸣⸣_ }
  PreOrder[mon] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → PreOrder (𝓁₁ ⊔ˡ 𝓁₂) (mon A B)
  PreOrder[mon] = record { _⊴_ = _⊴⸢mon⸣_ }

intro[⊑]⸢λ⸣ :
  ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f : ⟪ A ⟫ → ⟪ B ⟫} {f-proper : proper (_⊑_ ⇉ _⊑_) f} {g : ⟪ A ⟫ → ⟪ B ⟫} {g-proper : proper (_⊑_ ⇉ _⊑_) g}
  → (_⊑_ ⇉ _⊑_) f g → [λ f ] {f-proper} ⊴ [λ g ] {g-proper}
intro[⊑]⸢λ⸣ f⊑g = ↑⟨ f⊑g ⟩

elim[⊑]⸢λ⸣ : 
  ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f : ⟪ A ⟫ → ⟪ B ⟫} {f-proper : proper (_⊑_ ⇉ _⊑_) f} {g : ⟪ A ⟫ → ⟪ B ⟫} {g-proper : proper (_⊑_ ⇉ _⊑_) g}
  → [λ f ] {f-proper} ⊴ [λ g ] {g-proper} → (_⊑_ ⇉ _⊑_) f g
elim[⊑]⸢λ⸣ ↑⟨ f⊑g ⟩ = f⊑g

[λ↑_] : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {{PO : PreOrder 𝓁₁ A}} {B : POSet 𝓁₂} (f : A → ⟪ B ⟫) {f-proper : proper (_⊴_ ⇉ _⊑_) f} → mon (⇧ A) B
[λ↑ f ] {f-proper} = [λ f ∘ ↓ ] {ppr}
  where
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_) (f ∘ ↓)
      ppr = f-proper ∘ elim[⊑]⸢↓⸣

intro[⊑]⸢λ↑⸣ : 
  ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {{PO : PreOrder 𝓁₁ A}} {B : POSet 𝓁₂} {f : A → ⟪ B ⟫} {f-proper : proper (_⊴_ ⇉ _⊑_) f} {g : A → ⟪ B ⟫} {g-proper : proper (_⊴_ ⇉ _⊑_) g}
  → (_⊴_ ⇉ _⊑_) f g → [λ↑ f ] {f-proper} ⊴ [λ↑ g ] {g-proper}
intro[⊑]⸢λ↑⸣ f⊑g = ↑⟨ f⊑g ∘ elim[⊑]⸢↓⸣ ⟩

elim[⊑]⸢λ↑⸣ :
  ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {{PO : PreOrder 𝓁₁ A}} {B : POSet 𝓁₂} {f : A → ⟪ B ⟫} {f-proper : proper (_⊴_ ⇉ _⊑_) f} {g : A → ⟪ B ⟫} {g-proper : proper (_⊴_ ⇉ _⊑_) g}
  → [λ↑ f ] {f-proper} ⊴ [λ↑ g ] {g-proper} → (_⊴_ ⇉ _⊑_) f g
elim[⊑]⸢λ↑⸣ ↑⟨ f⊑g ⟩ = f⊑g ∘ intro[⊑]⸢↑⸣

infixr 4 _⇒_
_⇒_ : ∀ {𝓁₁ 𝓁₂} → POSet 𝓁₁ → POSet 𝓁₂ → POSet (𝓁₁ ⊔ˡ 𝓁₂)
A ⇒ B = ⇧ (mon A B)

infixl 20 _⋅_
_⋅_ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ A ⇒ B ⟫ → ⟪ A ⟫ → ⟪ B ⟫
_⋅_ (↑⟨ [λ f ] ⟩) = f

res-f-x[λ]⸢⊑⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f g : ⟪ A ⇒ B ⟫} {x y : ⟪ A ⟫} → f ⊑ g → x ⊑ y → f ⋅ x ⊑ g ⋅ y
res-f-x[λ]⸢⊑⸣ {f = ↑⟨ [λ f ] ⟩} {↑⟨ [λ g ] ⟩} {x} {y} f⊑g = elim[⊑]⸢λ⸣ $ elim[⊑]⸢↓⸣ f⊑g

res-x[λ]⸢⊑⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f : ⟪ A ⇒ B ⟫} {x y : ⟪ A ⟫} → x ⊑ y → f ⋅ x ⊑ f ⋅ y
res-x[λ]⸢⊑⸣ {f = f} = res-f-x[λ]⸢⊑⸣ $ xRx {x = f}

res-f[λ]⸢⊑⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f g : ⟪ A ⇒ B ⟫} {x : ⟪ A ⟫} → f ⊑ g → f ⋅ x ⊑ g ⋅ x 
res-f[λ]⸢⊑⸣ f⊑g = res-f-x[λ]⸢⊑⸣ f⊑g xRx

ext[λ]⸢⊑⸣ : ∀ {𝓁₁} {𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f g : ⟪ A ⇒ B ⟫} → (∀ {x : ⟪ A ⟫} → (f ⋅ x) ⊑ (g ⋅ x)) → f ⊑ g
ext[λ]⸢⊑⸣ {f = ↑⟨ [λ f ] {f-proper} ⟩} {g = ↑⟨ [λ g ] ⟩} f⊑g = intro[⊑]⸢↑⸣ (intro[⊑]⸢λ⸣ (λ x⊑y → f⊑g ⌾ f-proper x⊑y))

res-f-x[λ]⸢≈⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f g : ⟪ A ⇒ B ⟫} {x y : ⟪ A ⟫} → f ≈ g → x ≈ y → f ⋅ x ≈ g ⋅ y
res-f-x[λ]⸢≈⸣ f≈g x≈y = ⋈[] (res-f-x[λ]⸢⊑⸣ (xRx[] f≈g) (xRx[] x≈y)) (res-f-x[λ]⸢⊑⸣ (xRx[] $ ◇ f≈g) (xRx[] $ ◇ x≈y))

res-x[λ]⸢≈⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f : ⟪ A ⇒ B ⟫} {x y : ⟪ A ⟫} → x ≈ y → f ⋅ x ≈ f ⋅ y
res-x[λ]⸢≈⸣ {f = f} = res-f-x[λ]⸢≈⸣ $ xRx {x = f}

res-f[λ]⸢≈⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f g : ⟪ A ⇒ B ⟫} {x : ⟪ A ⟫} → f ≈ g → f ⋅ x ≈ g ⋅ x 
res-f[λ]⸢≈⸣ {x = x} f⊑g = res-f-x[λ]⸢≈⸣ f⊑g $ xRx {x = x}


ext[λ]⸢≈⸣ : ∀ {𝓁₁} {𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f g : ⟪ A ⇒ B ⟫} → (∀ {x : ⟪ A ⟫} → (f ⋅ x) ≈ (g ⋅ x)) → f ≈ g
ext[λ]⸢≈⸣ f≈g = ⋈[] (ext[λ]⸢⊑⸣ (xRx[] f≈g)) (ext[λ]⸢⊑⸣ (xRx[] $ ◇ f≈g))

mk[λ]-witness : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → ⟪ _⊑_ {A = ⟪ A ⟫} ⇉ _⊑_  {A = ⟪ B ⟫}⟫⸢W⸣ → ⟪ A ⇒ B ⟫
mk[λ]-witness f = ↑ $ [λ witness-x f ] {ppr}
  where
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_) (witness-x f)
      ppr = witness-proper f

mk[λ]-W[_,_] : ∀ {𝓁₁ 𝓁₂} (A : POSet 𝓁₁) (B : POSet 𝓁₂) → ⟪ (_⊑_ {A = ⟪ A ⟫} ⇉ _⊑_ {A = ⟪ B ⟫}) ⇉⸢W⸣ _⊑_ {A = ⟪ A ⇒ B ⟫}⟫⸢W⸣
mk[λ]-W[ A , B ] = mk[witness] mk[λ]-witness (intro[⊑]⸢↑⸣ ∘ intro[⊑]⸢λ⸣)

id⸢λ⸣ : ∀ {𝓁} {A : POSet 𝓁} → ⟪ _⊑_ {A = ⟪ A ⟫} ⇉⸢W⸣ _⊑_ {A = ⟪ A ⟫} ⟫⸢W⸣
id⸢λ⸣ = id⸢W⸣

curry⸢λ⸣ :
  ∀ {𝓁₁ 𝓁₂ 𝓁₂ʳ 𝓁₃} {A : POSet 𝓁₁} {B : Set 𝓁₂} {_R_ : relation 𝓁₂ʳ B} {C : POSet 𝓁₃}
  → _R_ ⇒⸢W⸣ _⊑_ {A = ⟪ C ⟫}
  → (_⊑_ {A = ⟪ A ⟫} ⇉ _R_) ⇒⸢W⸣ _⊑_ {A = ⟪ A ⇒ C ⟫}
curry⸢λ⸣ {A = A} {B} {_R_} {C} g = mk[λ]-W[ A , C ] ⌾[D]⸢W⸣[ _⊑_ ⇉ _R_ , _⊑_ ⇉ _⊑_ , _⊑_ ] compose[DR₁]⸢W⸣[ _⊑_ , _R_ , _⊑_ ] ⋅⸢W⸣ g

mk[λ↑]-witness : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {{PO : PreOrder 𝓁₁ A}} {B : POSet 𝓁₂} → ⟪ _⊴_ {A = A} ⇉ _⊑_  {A = ⟪ B ⟫}⟫⸢W⸣ → ⟪ ⇧ A ⇒ B ⟫
mk[λ↑]-witness f = ↑ $ [λ↑ witness-x f ] {ppr}
  where
    abstract
      ppr : proper (_⊴_ ⇉ _⊑_) (witness-x f)
      ppr = witness-proper f

mk[λ↑]-W[_,_] : ∀ {𝓁₁ 𝓁₂} (A : Set 𝓁₁) {{PO : PreOrder 𝓁₁ A}} (B : POSet 𝓁₂) → ⟪ (_⊴_ {A = A} ⇉ _⊑_ {A = ⟪ B ⟫}) ⇉⸢W⸣ _⊑_ {A = ⟪ ⇧ A ⇒ B ⟫}⟫⸢W⸣
mk[λ↑]-W[ A , B ] = mk[witness] mk[λ↑]-witness (intro[⊑]⸢↑⸣ ∘ intro[⊑]⸢λ↑⸣)

id⸢λ↑⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} → ⟪ _⊴_ {A = A} ⇉⸢W⸣ _⊑_ {A = ⟪ ⇧ A ⟫} ⟫⸢W⸣
id⸢λ↑⸣ = mk[witness] (↑ ∘ witness-x) intro[⊑]⸢↑⸣

curry⸢λ↑⸣ :
  ∀ {𝓁₁ 𝓁₂ 𝓁₂ʳ 𝓁₃} {A : Set 𝓁₁} {{PO : PreOrder 𝓁₁ A}} {{REX : Reflexive (_⊴_ {A = A})}} {B : Set 𝓁₂} {_R_ : relation 𝓁₂ʳ B} {C : POSet 𝓁₃}
  → _R_ ⇒⸢W⸣ _⊑_ {A = ⟪ C ⟫}
  → (_⊴_ {A = A} ⇉ _R_) ⇒⸢W⸣ _⊑_ {A = ⟪ ⇧ A ⇒ C ⟫}
curry⸢λ↑⸣ {A = A} {B = B} {_R_} {C} g = mk[λ↑]-W[ A , C ] ⌾[D]⸢W⸣[ _⊴_ ⇉ _R_ , _⊴_ ⇉ _⊑_ , _⊑_ ] compose[DR₁]⸢W⸣[ _⊴_ , _R_ , _⊑_ {A = ⟪ C ⟫} ] ⋅⸢W⸣ g

-- for posterity, because who can tell w.t.f. mk[λ]-curry is curry⸢λ⸣... -DCD
curry-arg-old :
  ∀ {𝓁₁ 𝓁₂ 𝓁₂ʳ 𝓁₃} {A : POSet 𝓁₁} {B : Set 𝓁₂} {_R_ : relation 𝓁₂ʳ B} {C : POSet 𝓁₃}
  → _R_ ⇒⸢W⸣ _⊑_ {A = ⟪ C ⟫}
  → (_⊑_ {A = ⟪ A ⟫} ⇉ _R_) ⇒⸢W⸣ _⊑_ {A = ⟪ A ⇒ C ⟫}
curry-arg-old {A = A} {B} {_R_} {C} (mk[witness] g g-proper) = mk[witness] t ppr
  where
    t : ⟪ _⊑_ {A = ⟪ A ⟫} ⇉ _R_ ⟫⸢W⸣ → ⟪ A ⇒ C ⟫
    t (mk[witness] f f-proper) = ↑ $ [λ (λ x → g (mk[witness] (f x) (f-proper xRx))) ] {ppr}
      where
        abstract
          ppr : proper (_⊑_ ⇉ _⊑_) (λ x → g (mk[witness] (f x) (f-proper xRx)))
          ppr = g-proper ∘ f-proper
    abstract
      ppr : proper ((_⊑_ ⇉ _R_) ⇉⸢W⸣ _⊑_) t
      ppr f₁⊑f₂ = ↑⟨ intro[⊑]⸢λ⸣ (g-proper ∘ f₁⊑f₂) ⟩
