module Poset.Power where

open import Prelude
open import Poset.Poset
open import Poset.Fun

infix 14 _⋿_

data ℘♭ {ℓ} (A : Poset ℓ) : Set (↑ᴸ ℓ) where
  [ω_] : (φ : ⟪ A ⟫ → Set ℓ) → {φ-proper : proper (_⊒♮_ ⇉ [→]) φ} → ℘♭ A

data _≼⸢℘♭⸣_ {ℓ} {A : Poset ℓ} : relation (↑ᴸ ℓ) (℘♭ A) where
  ♮⟨_⟩ :
    ∀ {φ₁ : ⟪ A ⟫ → Set ℓ} {φ₁-proper : proper (_⊒♮_ ⇉ [→]) φ₁} {φ₂ : ⟪ A ⟫ → Set ℓ} {φ₂-proper : proper (_⊒♮_ ⇉ [→]) φ₂}
    → (_⊒♮_ ⇉ [→]) φ₁ φ₂ → [ω φ₁ ] {φ₁-proper} ≼⸢℘♭⸣ [ω φ₂ ] {φ₂-proper}

xRx⸢≼℘♭⸣ : ∀ {ℓ} {A : Poset ℓ} → reflexive (_≼⸢℘♭⸣_ {A = A})
xRx⸢≼℘♭⸣ {x = [ω X ] {X-proper}} = ♮⟨ X-proper ⟩

_⊚⸢≼℘♭⸣_ : ∀ {ℓ} {A : Poset ℓ} → transitive (_≼⸢℘♭⸣_ {A = A})
♮⟨ Y≼Z ⟩ ⊚⸢≼℘♭⸣ ♮⟨ X≼Y ⟩ = ♮⟨ (λ x⊒y → Y≼Z xRx⸢⊑♮⸣ ∘ X≼Y x⊒y) ⟩

instance
  Reflexive[℘♭] : ∀ {ℓ} {A : Poset ℓ} → Reflexive (_≼⸢℘♭⸣_ {A = A})
  Reflexive[℘♭] = record { xRx = xRx⸢≼℘♭⸣ }
  Transitive[℘♭] : ∀ {ℓ} {A : Poset ℓ} → Transitive (_≼⸢℘♭⸣_ {A = A})
  Transitive[℘♭] = record { _⊚_ = _⊚⸢≼℘♭⸣_ }
  PreOrder[℘♭] : ∀ {ℓ} {A : Poset ℓ} → PreOrder (↑ᴸ ℓ) (℘♭ A)
  PreOrder[℘♭] = record { _≼_ = _≼⸢℘♭⸣_ }

module _ {ℓ} {A : Poset ℓ} {X : ⟪ A ⟫ → Set ℓ} {X-proper : proper (_⊒♮_ ⇉ [→]) X} {Y : ⟪ A ⟫ → Set ℓ} {Y-proper : proper (_⊒♮_ ⇉ [→]) Y} where
  intro[⊑♮]⸢℘⸣ : (_⊒♮_ ⇉ [→]) X Y → [ω X ] {X-proper} ≼ [ω Y ] {Y-proper}
  intro[⊑♮]⸢℘⸣ X⊑Y = ♮⟨ X⊑Y ⟩
  
  elim[⊑♮]⸢℘⸣ : [ω X ] {X-proper} ≼ [ω Y ] {Y-proper} → (_⊒♮_ ⇉ [→]) X Y
  elim[⊑♮]⸢℘⸣ ♮⟨ X⊑Y ⟩ = X⊑Y

[ω♭_] : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} (X : A → Set ℓ) {X-proper : proper (_≽_ ⇉ [→]) X} → ℘♭ (⇧ A)
[ω♭ X ] {X-proper} = [ω X ∘ ♭ ] {ppr}
  where
    abstract
      ppr : proper (_⊒♮_ ⇉ [→]) (X ∘ ♭)
      ppr = X-proper ∘ elim[⊑♭]

module _ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} {X : A → Set ℓ} {X-proper : proper (_≽_ ⇉ [→]) X} {Y : A → Set ℓ} {Y-proper : proper (_≽_ ⇉ [→]) Y} where
  intro[⊑℘♭] : (_≽_ ⇉ [→]) X Y → [ω♭ X ] {X-proper} ≼ [ω♭ Y ] {Y-proper}
  intro[⊑℘♭] X⊑Y = ♮⟨ X⊑Y ∘ elim[⊑♭] ⟩
  
  elim[⊑℘♭] : [ω♭ X ] {X-proper} ≼ [ω♭ Y ] {Y-proper} → (_≽_ ⇉ [→]) X Y
  elim[⊑℘♭] ♮⟨ X⊑Y ⟩ = X⊑Y ∘ intro[⊑♮]

℘ : ∀ {ℓ} → Poset ℓ → Poset (↑ᴸ ℓ)
℘ A = ⇧ (℘♭ A)

_⋿_ : ∀ {ℓ} {A : Poset ℓ} → ⟪ A ⟫ → ⟪ ℘ A ⟫ → Set ℓ
x ⋿ ♮⟨ [ω X ] ⟩ = X x

module _ {ℓ} {A : Poset ℓ} where
  res[Xx]⸢⊑℘⸣ : ∀ {X Y : ⟪ ℘ A ⟫} {x y : ⟪ A ⟫} → X ⊑♮ Y → x ⊒♮ y → x ⋿ X → y ⋿ Y
  res[Xx]⸢⊑℘⸣ {X = ♮⟨ [ω X ] ⟩} {♮⟨ [ω Y ] ⟩} X⊑Y = elim[⊑♮]⸢℘⸣ $ elim[⊑♮] X⊑Y
  
  res[x]⸢⊑℘⸣ : ∀ {X : ⟪ ℘ A ⟫} {x y : ⟪ A ⟫} → x ⊒♮ y → x ⋿ X → y ⋿ X
  res[x]⸢⊑℘⸣ {X = X} = res[Xx]⸢⊑℘⸣ (xRx {x = X})
  
  res[X]⸢⊑℘⸣ : ∀ {X Y : ⟪ ℘ A ⟫} {x : ⟪ A ⟫} → X ⊑♮ Y → x ⋿ X → x ⋿ Y
  res[X]⸢⊑℘⸣ X⊑Y = res[Xx]⸢⊑℘⸣ X⊑Y xRx

  ext⸢⊑℘⸣ : ∀ {X Y : ⟪ ℘ A ⟫} → (∀ {x} → x ⋿ X → x ⋿ Y) → X ⊑♮ Y
  ext⸢⊑℘⸣ {X = ♮⟨ [ω X ] {X-proper} ⟩} {♮⟨ [ω Y ] ⟩} X⊑Y = intro[⊑♮] (intro[⊑♮]⸢℘⸣ (λ x⊒y → X⊑Y ∘ X-proper x⊒y))
  
  res[Xx]⸢≈℘⸣ : ∀ {X Y : ⟪ ℘ A ⟫} {x y : ⟪ A ⟫} → X ≈♮ Y → x ≈♮ y → x ⋿ X ↔ y ⋿ Y
  res[Xx]⸢≈℘⸣ X≈Y x≈y = (res[Xx]⸢⊑℘⸣ (xRx[] X≈Y) (xRx[] $ ◇ x≈y)) , res[Xx]⸢⊑℘⸣ (xRx[] $ ◇ X≈Y) (xRx[] x≈y)
  
  res[x]⸢≈℘⸣ : ∀ {X : ⟪ ℘ A ⟫} {x y : ⟪ A ⟫} → x ≈♮ y → x ⋿ X ↔ y ⋿ X
  res[x]⸢≈℘⸣ {X = X} = res[Xx]⸢≈℘⸣ $ xRx {x = X}
  
  res[X]⸢≈℘⸣ : ∀ {X Y : ⟪ ℘ A ⟫} {x : ⟪ A ⟫} → X ≈♮ Y → x ⋿ X ↔ x ⋿ Y
  res[X]⸢≈℘⸣ {x = x} X⊑Y = res[Xx]⸢≈℘⸣ X⊑Y $ xRx {x = x}
  
  ext⸢≈℘⸣ : ∀ {X Y : ⟪ ℘ A ⟫} → (∀ {x} → x ⋿ X ↔ x ⋿ Y) → X ≈♮ Y
  ext⸢≈℘⸣ X≈Y = ⋈[] (ext⸢⊑℘⸣ (π₁ X≈Y)) (ext⸢⊑℘⸣ (π₂ X≈Y))

mk[ω]-witness : ∀ {ℓ} {A : Poset ℓ} → ⟪ _⊒♮_ {A = A} ⇉ [→] {ℓ} ⟫ʷ → ⟪ ℘ A ⟫
mk[ω]-witness X = ♮ $ [ω witness X ] {ppr}
  where
    abstract
      ppr : proper (_⊒♮_ ⇉ [→]) (witness X)
      ppr = proper[witness] X

id⸢ω⸣ : ∀ {ℓ} {A : Poset ℓ} → ⟪ (_⊒♮_ {A = A} ⇉ [→] {ℓ}) ⇉ʷ _⊑♮_ {A = ℘ A}⟫ʷ
id⸢ω⸣ = mk[witness] mk[ω]-witness (intro[⊑♮] ∘ intro[⊑♮]⸢℘⸣)

curry⸢ω⸣[_] : ∀ {ℓ ℓʳ} {A : Set ℓ} {_R_ : relation ℓʳ A} {B : Poset ℓ} → ⟪ _⊑♮_ {A = B} ⇉ʷ _R_ ⟫ʷ → ⟪ (flip _R_ ⇉ [→] {ℓ}) ⇉ʷ _⊑♮_ {A = ℘ B} ⟫ʷ
curry⸢ω⸣[_] {A = A} {_R_} {B} f = id⸢ω⸣ ⊚[D]ʷ[ flip _R_ ⇉ [→] , _⊒♮_ ⇉ [→] , _⊑♮_ ] pipe[DR₁]ʷ[ _⊒♮_ , flip _R_ , [→] ] {{record { xRx = xRx }}} ⋅ʷ flipʷ[ _⊑♮_ , _R_ ] f

id⸢ω♭⸣ : ∀ {ℓ} {A : Set ℓ} {{_ : PreOrder ℓ A}} → ⟪ (_≽_ {A = A} ⇉ [→] {ℓ}) ⇉ʷ _⊑♮_ {A = ℘ (⇧ A)}⟫ʷ
id⸢ω♭⸣ = curry⸢ω⸣[ <♭> ]

-- mk[ω♭]-witness : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} → ⟪ _≽_ {A = A} ⇉ [→] {ℓ}⟫ʷ → ⟪ ℘ (⇧ A) ⟫
-- mk[ω♭]-witness X = ♮ $ [ω♭ witness X ] {ppr}
--   where
--     abstract
--       ppr : proper (_≽_ ⇉ [→]) (witness X)
--       ppr = proper[witness] X
-- 
-- id⸢ω♭⸣ : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} → ⟪ (_≽_ {A = A} ⇉ [→] {ℓ}) ⇉ʷ _⊑_ {A = ℘ (⇧ A)}⟫ʷ
-- id⸢ω♭⸣ = mk[witness] mk[ω♭]-witness (intro[⊑♮] ∘ intro[⊑℘♭])
