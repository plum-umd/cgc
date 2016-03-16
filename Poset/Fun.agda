module Poset.Fun where

open import Prelude
open import Poset.Poset
open import Data.Witness public

infixr 11 _↗_
infixl 50 _⋅_

data _↗♭_ {ℓ₁ ℓ₂} (A : Poset ℓ₁) (B : Poset ℓ₂) : Set (ℓ₁ ⊔ᴸ ℓ₂) where
  [λ_] : (f : ⟪ A ⟫  → ⟪ B ⟫) → {f-proper : proper (_⊑♮_ ⇉ _⊑♮_) f} → A ↗♭ B

data _≼⸢↗♭⸣_ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} : relation (ℓ₁ ⊔ᴸ ℓ₂) (A ↗♭ B) where
  ♮⟨_⟩ :
    ∀ {f : ⟪ A ⟫ → ⟪ B ⟫} {f-proper : proper (_⊑♮_ ⇉ _⊑♮_) f}
    {g : ⟪ A ⟫ → ⟪ B ⟫} {g-proper : proper (_⊑♮_ ⇉ _⊑♮_) g}
    → (_⊑♮_ ⇉ _⊑♮_) f g → [λ f ] {f-proper} ≼⸢↗♭⸣ [λ g ] {g-proper}

xRx⸢≼↗♭⸣ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → reflexive (_≼⸢↗♭⸣_ {A = A} {B})
xRx⸢≼↗♭⸣ {x = [λ f ] {f-proper}} = ♮⟨ f-proper ⟩

_⊚⸢≼↗♭⸣_ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → transitive (_≼⸢↗♭⸣_ {A = A} {B})
♮⟨ g⊑h ⟩ ⊚⸢≼↗♭⸣ ♮⟨ f⊑g ⟩ = ♮⟨ (λ x⊑y → g⊑h xRx ⊚⸢⊑♮⸣ f⊑g x⊑y) ⟩

instance
  Reflexive[↗♭] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → Reflexive (_≼⸢↗♭⸣_ {A = A} {B})
  Reflexive[↗♭] = record { xRx = xRx⸢≼↗♭⸣ }
  Transitive[↗♭] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → Transitive (_≼⸢↗♭⸣_ {A = A} {B})
  Transitive[↗♭] = record { _⊚_ = _⊚⸢≼↗♭⸣_ }
  PreOrder[↗♭] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → PreOrder (ℓ₁ ⊔ᴸ ℓ₂) (A ↗♭ B)
  PreOrder[↗♭] = record { _≼_ = _≼⸢↗♭⸣_ }

module _
  {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂}
  {f : ⟪ A ⟫ → ⟪ B ⟫} {f-proper : proper (_⊑♮_ ⇉ _⊑♮_) f}
  {g : ⟪ A ⟫ → ⟪ B ⟫} {g-proper : proper (_⊑♮_ ⇉ _⊑♮_) g} where

  intro[⊑↗] : (_⊑♮_ ⇉ _⊑♮_) f g → [λ f ] {f-proper} ≼ [λ g ] {g-proper}
  intro[⊑↗] f⊑g = ♮⟨ f⊑g ⟩
  
  elim[⊑↗] : [λ f ] {f-proper} ≼ [λ g ] {g-proper} → (_⊑♮_ ⇉ _⊑♮_) f g
  elim[⊑↗] ♮⟨ f⊑g ⟩ = f⊑g

[λ♭_] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {{PO : PreOrder ℓ₁ A}} {B : Poset ℓ₂} (f : A → ⟪ B ⟫) {f-proper : proper (_≼_ ⇉ _⊑♮_) f} → ⇧ A ↗♭ B
[λ♭ f ] {f-proper} = [λ f ∘ ♭ ] {ppr}
  where
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_) (f ∘ ♭)
      ppr = f-proper ∘ elim[⊑♭]

module _
  {ℓ₁ ℓ₂} {A : Set ℓ₁} {{PO : PreOrder ℓ₁ A}} {B : Poset ℓ₂}
  {f : A → ⟪ B ⟫} {f-proper : proper (_≼_ ⇉ _⊑♮_) f}
  {g : A → ⟪ B ⟫} {g-proper : proper (_≼_ ⇉ _⊑♮_) g} where

  intro[⊑↗♭] : (_≼_ ⇉ _⊑♮_) f g → [λ♭ f ] {f-proper} ≼ [λ♭ g ] {g-proper}
  intro[⊑↗♭] f⊑g = ♮⟨ f⊑g ∘ elim[⊑♭] ⟩
  
  elim[⊑↗♭] : [λ♭ f ] {f-proper} ≼ [λ♭ g ] {g-proper} → (_≼_ ⇉ _⊑♮_) f g
  elim[⊑↗♭] ♮⟨ f⊑g ⟩ = f⊑g ∘ intro[⊑♮]

_↗_ : ∀ {ℓ₁ ℓ₂} → Poset ℓ₁ → Poset ℓ₂ → Poset (ℓ₁ ⊔ᴸ ℓ₂)
A ↗ B = ⇧ (A ↗♭ B)

_⋅_ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → ⟪ A ↗ B ⟫ → ⟪ A ⟫ → ⟪ B ⟫
_⋅_ (♮⟨ [λ f ] ⟩) = f

module _ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} where
  res[fx]⸢⊑↗⸣ : ∀ {f g : ⟪ A ↗ B ⟫} {x y : ⟪ A ⟫} → f ⊑♮ g → x ⊑♮ y → f ⋅ x ⊑♮ g ⋅ y
  res[fx]⸢⊑↗⸣ {f = ♮⟨ [λ f ] ⟩} {♮⟨ [λ g ] ⟩} {x} {y} f⊑g = elim[⊑↗] $ elim[⊑♭] f⊑g
  
  res[x]⸢⊑↗⸣ : ∀ {f : ⟪ A ↗ B ⟫} {x y : ⟪ A ⟫} → x ⊑♮ y → f ⋅ x ⊑♮ f ⋅ y
  res[x]⸢⊑↗⸣ {f = f} = res[fx]⸢⊑↗⸣ $ xRx {x = f}
  
  res[f]⸢⊑↗⸣ : ∀ {f g : ⟪ A ↗ B ⟫} {x : ⟪ A ⟫} → f ⊑♮ g → f ⋅ x ⊑♮ g ⋅ x 
  res[f]⸢⊑↗⸣ f⊑g = res[fx]⸢⊑↗⸣ f⊑g xRx
  
  ext⸢⊑↗⸣ : ∀ {f g : ⟪ A ↗ B ⟫} → (∀ {x : ⟪ A ⟫} → (f ⋅ x) ⊑♮ (g ⋅ x)) → f ⊑♮ g
  ext⸢⊑↗⸣ {f = ♮⟨ [λ f ] {f-proper} ⟩} {g = ♮⟨ [λ g ] ⟩} f⊑g = intro[⊑♮] (intro[⊑↗] (λ x⊑y → f⊑g ⊚ f-proper x⊑y))
  
  res[fx]⸢≈↗⸣ : ∀ {f g : ⟪ A ↗ B ⟫} {x y : ⟪ A ⟫} → f ≈♮ g → x ≈♮ y → f ⋅ x ≈♮ g ⋅ y
  res[fx]⸢≈↗⸣ f≈g x≈y = ⋈[] (res[fx]⸢⊑↗⸣ (xRx[≈]⸢⊑♮⸣ f≈g) (xRx[] x≈y)) (res[fx]⸢⊑↗⸣ (xRx[≈]⸢⊑♮⸣ $ ◇⸢≈♮⸣ f≈g) (xRx[] $ ◇ x≈y))
  
  res[x]⸢≈↗⸣ : ∀ {f : ⟪ A ↗ B ⟫} {x y : ⟪ A ⟫} → x ≈♮ y → f ⋅ x ≈♮ f ⋅ y
  res[x]⸢≈↗⸣ {f = f} = res[fx]⸢≈↗⸣ $ xRx {x = f}
  
  res[f]⸢≈↗⸣ : ∀ {f g : ⟪ A ↗ B ⟫} {x : ⟪ A ⟫} → f ≈♮ g → f ⋅ x ≈♮ g ⋅ x 
  res[f]⸢≈↗⸣ {x = x} f⊑g = res[fx]⸢≈↗⸣ f⊑g $ xRx {x = x}
  
  ext⸢≈↗⸣ : ∀ {f g : ⟪ A ↗ B ⟫} → (∀ {x : ⟪ A ⟫} → (f ⋅ x) ≈♮ (g ⋅ x)) → f ≈♮ g
  ext⸢≈↗⸣ f≈g = ⋈[≈]⸢⊑♮⸣ (ext⸢⊑↗⸣ (xRx[] f≈g)) (ext⸢⊑↗⸣ (xRx[] $ ◇ f≈g))

mk[λ]-witness : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → ⟪ _⊑♮_ {A = A} ⇉ _⊑♮_ {A = B}⟫ʷ → ⟪ A ↗ B ⟫
mk[λ]-witness f = ♮ $ [λ witness f ] {ppr}
  where
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_) (witness f)
      ppr = proper[witness] f

mk[λ]-W[_,_] : ∀ {ℓ₁ ℓ₂} (A : Poset ℓ₁) (B : Poset ℓ₂) → ⟪ (_⊑♮_ {A = A} ⇉ _⊑♮_ {A = B}) ⇉ʷ _⊑♮_ {A = A ↗ B}⟫ʷ
mk[λ]-W[ A , B ] = mk[witness] mk[λ]-witness (intro[⊑♮] ∘ intro[⊑↗])

id⸢λ⸣ : ∀ {ℓ} {A : Poset ℓ} → ⟪ _⊑♮_ {A = A} ⇉ʷ _⊑♮_ {A = A} ⟫ʷ
id⸢λ⸣ = idʷ

curry⸢λ⸣[_] : 
  ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₃ ℓ₃ʳ ℓ₄} {A : Set ℓ₁} {_R₁_ : relation ℓ₁ʳ A} {B : Poset ℓ₂} {C : Set ℓ₃} {_R₂_ : relation ℓ₃ʳ C} {D : Poset ℓ₄}
  → ⟪ _⊑♮_ {A = B} ⇉ʷ _R₁_ ⟫ʷ
  → {{_ : Reflexive _R₁_}}
  → ⟪ _R₂_ ⇉ʷ _⊑♮_ {A = D} ⟫ʷ
  → ⟪ (_R₁_ ⇉ _R₂_) ⇉ʷ _⊑♮_ {A = B ↗ D} ⟫ʷ
curry⸢λ⸣[_] {A = A} {_R₁_} {B} {C} {_R_} {D} g f =
   mk[λ]-W[ B , D ]
   ⊚[D]ʷ[ _R₁_ ⇉ _R_ , _⊑♮_ ⇉ _⊑♮_ , _⊑♮_ {A = B ↗ D} ]
   (pipe[DR₁]ʷ[ _⊑♮_ , _R₁_ , _⊑♮_ ] ⋅ʷ g)
   ⊚[D]ʷ[ _R₁_ ⇉ _R_ , _R₁_ ⇉ _⊑♮_ , _⊑♮_ ⇉ _⊑♮_ ]
   compose[DR₁]ʷ[ _R₁_ , _R_ , _⊑♮_ ] ⋅ʷ f

<♭> : ∀ {ℓ} {A : Set ℓ} {{_ : PreOrder ℓ A}} → ⟪ _⊑♮_ {A = ⇧ A} ⇉ʷ _≼_ {A = A} ⟫ʷ
<♭> = mk[witness] (♭ ∘ witness) elim[⊑♭]

<♮> : ∀ {ℓ} {A : Set ℓ} {{_ : PreOrder ℓ A}} → ⟪ _≼_ {A = A} ⇉ʷ _⊑♮_ {A = ⇧ A} ⟫ʷ
<♮> = mk[witness] (♮ ∘ witness) intro[⊑♮]

<id> : ∀ {ℓ} {A : Poset ℓ} → ⟪ _⊑♮_ {A = A} ⇉ʷ _⊑♮_ {A = A} ⟫ʷ
<id> = id⸢λ⸣

curry⸢λ⸣ :
  ∀ {ℓ₁ ℓ₂ ℓ₂ʳ} {A : Poset ℓ₁} {B : Set ℓ₂} {_R_ : relation ℓ₂ʳ B} {C : Poset ℓ₂}
  → ⟪ _R_ ⇉ʷ _⊑♮_ {A = C} ⟫ʷ
  → ⟪ (_⊑♮_ {A = A} ⇉ _R_) ⇉ʷ _⊑♮_ {A = A ↗ C} ⟫ʷ
curry⸢λ⸣ {A = A} {B} {_R_} {C} g = curry⸢λ⸣[ <id> ] g

id⸢λ♭⸣ : ∀ {ℓ} {A : Set ℓ} {{_ : PreOrder ℓ A}} → ⟪ _≼_ {A = A} ⇉ʷ _⊑♮_ {A = ⇧ A} ⟫ʷ
id⸢λ♭⸣ = <♮>

curry⸢λ♭⸣ :
  ∀ {ℓ₁ ℓ₂ ℓ₂ʳ} {A : Set ℓ₁} {{_ : PreOrder ℓ₁ A}} {B : Set ℓ₂} {_R_ : relation ℓ₂ʳ B} {C : Poset ℓ₂}
  → ⟪ _R_ ⇉ʷ _⊑♮_ {A = C} ⟫ʷ
  → ⟪ (_≼_ {A = A} ⇉ _R_) ⇉ʷ _⊑♮_ {A = ⇧ A ↗ C} ⟫ʷ
curry⸢λ♭⸣ = curry⸢λ⸣[ <♭> ] {{Reflexive[≼]}}

-- curry⸢λ⸣ :
--   ∀ {ℓ₁ ℓ₂ ℓ₂ʳ ℓ₃} {A : Poset ℓ₁} {B : Set ℓ₂} {_R_ : relation ℓ₂ʳ B} {C : Poset ℓ₃}
--   → _R_ ↗ʷ _⊑_ {A = C}
--   → (_⊑_ {A = A} ⇉ _R_) ↗ʷ _⊑_ {A = A ↗ C}
-- curry⸢λ⸣ {A = A} {B} {_R_} {C} g = mk[λ]-W[ A , C ] ⊚[D]ʷ[ _⊑_ ⇉ _R_ , _⊑_ ⇉ _⊑_ , _⊑_ ] compose[DR₁]ʷ[ _⊑_ , _R_ , _⊑_ ] ⋅ʷ g
-- 
-- mk[λ♮]-witness : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {{PO : PreOrder ℓ₁ A}} {B : Poset ℓ₂} → ⟪ _≼_ {A = A} ⇉ _⊑_  {A = B}⟫ʷ → ⟪ ⇧ A ↗ B ⟫
-- mk[λ♮]-witness f = ♮ $ [λ♮ witness f ] {ppr}
--   where
--     abstract
--       ppr : proper (_≼_ ⇉ _⊑_) (witness f)
--       ppr = proper[witness] f
-- 
-- mk[λ♮]-W[_,_] : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) {{PO : PreOrder ℓ₁ A}} (B : Poset ℓ₂) → ⟪ (_≼_ {A = A} ⇉ _⊑_ {A = B}) ⇉ʷ _⊑_ {A = ⇧ A ↗ B}⟫ʷ
-- mk[λ♮]-W[ A , B ] = mk[witness] mk[λ♮]-witness (intro[⊑♮] ∘ intro[⊑]⸢↗♮⸣)
-- 
-- id⸢λ♮⸣ : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} → ⟪ _≼_ {A = A} ⇉ʷ _⊑_ {A = ⇧ A} ⟫ʷ
-- id⸢λ♮⸣ = mk[witness] (♮ ∘ witness) intro[⊑♮]
-- 
-- curry⸢λ♮⸣ :
--   ∀ {ℓ₁ ℓ₂ ℓ₂ʳ ℓ₃} {A : Set ℓ₁} {{PO : PreOrder ℓ₁ A}} {{REX : Reflexive (_≼_ {A = A})}} {B : Set ℓ₂} {_R_ : relation ℓ₂ʳ B} {C : Poset ℓ₃}
--   → _R_ ↗ʷ _⊑_ {A = C}
--   → (_≼_ {A = A} ⇉ _R_) ↗ʷ _⊑_ {A = ⇧ A ↗ C}
-- curry⸢λ♮⸣ {A = A} {B = B} {_R_} {C} g = mk[λ♮]-W[ A , C ] ⊚[D]ʷ[ _≼_ ⇉ _R_ , _≼_ ⇉ _⊑_ , _⊑_ ] compose[DR₁]ʷ[ _≼_ , _R_ , _⊑_ {A = C} ] ⋅ʷ g
