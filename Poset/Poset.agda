module Poset.Poset where

open import Prelude

infix 14 _⊑♮_
infix 14 _⊒♮_
infix 14 _≈♮_
infixr 30 _⊚⸢⊑♮⸣_
infixr 30 _⊚⸢≈♮⸣_

data Poset ℓ : Set (↑ᴸ ℓ) where
  ⇧ : (A : Set ℓ) → {{_ : Precision ℓ A}} → Poset ℓ

dom : ∀ {ℓ} → Poset ℓ → Set ℓ
dom (⇧ A) = A

syntax ⊑ᵈ[] A x y = x ⊑ᵈ[ A ] y
⊑ᵈ[] : ∀ {ℓ} (A : Poset ℓ) → relation ℓ (dom A)
⊑ᵈ[] (⇧ A) x y = x ⊑ y

data ⟪_⟫ {ℓ} (A : Poset ℓ) : Set ℓ where
  ♮⟨_⟩ : dom A → ⟪ A ⟫

♮ : ∀ {ℓ} {A : Set ℓ} {{_ : Precision ℓ A}} → A → ⟪ ⇧ A ⟫
♮ = ♮⟨_⟩

♭ : ∀ {ℓ} {A : Set ℓ} {{_ : Precision ℓ A}} → ⟪ ⇧ A ⟫ → A
♭ (♮⟨ A ⟩) = A

data _⊑♮_ {ℓ} {A : Poset ℓ} : relation ℓ ⟪ A ⟫ where
  ♮⟨_⟩ : {x y : dom A} → x ⊑ᵈ[ A ] y → ♮⟨ x ⟩ ⊑♮ ♮⟨ y ⟩

_⊒♮_ : ∀ {ℓ} {A : Poset ℓ} → relation ℓ ⟪ A ⟫
_⊒♮_ = flip _⊑♮_

data _≈♮_ {ℓ} {A : Poset ℓ} : relation ℓ ⟪ A ⟫ where
  ⟨_,_⟩ : ∀ {x y} → x ⊑♮ y → y ⊑♮ x → x ≈♮ y

xRx⸢⊑♮⸣ : ∀ {ℓ} {A : Poset ℓ} → reflexive (_⊑♮_ {A = A})
xRx⸢⊑♮⸣ {A = ⇧ A {{A-PO}}} {x = ♮⟨ x ⟩} = ♮⟨ xRx[⊑] {{A-PO}} ⟩

_⊚⸢⊑♮⸣_ : ∀ {ℓ} {A : Poset ℓ} → transitive (_⊑♮_ {A = A})
_⊚⸢⊑♮⸣_ {A = ⇧ A {{A-PO}}} ♮⟨ y≼z ⟩ ♮⟨ x≼y ⟩ = ♮⟨ _⊚[⊑]_ {{A-PO}} y≼z x≼y ⟩

xRx[≈]⸢⊑♮⸣ : ∀ {ℓ} {A : Poset ℓ} → reflexiveᴳ _≈♮_ (_⊑♮_ {A = A})
xRx[≈]⸢⊑♮⸣ ⟨ x⊑y , _ ⟩ = x⊑y

⋈[≈]⸢⊑♮⸣ : ∀ {ℓ} {A : Poset ℓ} → antisymmetricᴳ _≈♮_ (_⊑♮_ {A = A})
⋈[≈]⸢⊑♮⸣ = ⟨_,_⟩

xRx⸢≈♮⸣ : ∀ {ℓ} {A : Poset ℓ} → reflexive (_≈♮_ {A = A})
xRx⸢≈♮⸣ = ⟨ xRx⸢⊑♮⸣ , xRx⸢⊑♮⸣ ⟩

_⊚⸢≈♮⸣_ : ∀ {ℓ} {A : Poset ℓ} → transitive (_≈♮_ {A = A})
⟨ y⊑z , z⊑y ⟩ ⊚⸢≈♮⸣ ⟨ x⊑y , y⊑x ⟩ = ⟨ y⊑z ⊚⸢⊑♮⸣ x⊑y , y⊑x ⊚⸢⊑♮⸣ z⊑y ⟩

◇⸢≈♮⸣ : ∀ {ℓ} {A : Poset ℓ} → symmetric (_≈♮_ {A = A})
◇⸢≈♮⸣ ⟨ x⊑y , y⊑x ⟩ = ⟨ y⊑x , x⊑y ⟩

instance
  Reflexive[⊑♮] : ∀ {ℓ} {A : Poset ℓ} → Reflexive (_⊑♮_ {A = A})
  Reflexive[⊑♮] = record { xRx = xRx⸢⊑♮⸣ }
  Transitive[⊑♮] : ∀ {ℓ} {A : Poset ℓ} → Transitive (_⊑♮_ {A = A})
  Transitive[⊑♮] = record { _⊚_ = _⊚⸢⊑♮⸣_ }
  Reflexive[≈][⊑♮] : ∀ {ℓ} {A : Poset ℓ} → Reflexiveᴳ _≈♮_ (_⊑♮_ {A = A})
  Reflexive[≈][⊑♮] = record { xRxᴳ = xRx[≈]⸢⊑♮⸣ }
  Antisymmetric[≈][⊑♮] : ∀ {ℓ} {A : Poset ℓ} → Antisymmetricᴳ _≈♮_ (_⊑♮_ {A = A})
  Antisymmetric[≈][⊑♮] = record { ⋈ᴳ = ⋈[≈]⸢⊑♮⸣ }
  Reflexive[≈♮] : ∀ {ℓ} {A : Poset ℓ} → Reflexive (_≈♮_ {A = A})
  Reflexive[≈♮] = record { xRx = xRx⸢≈♮⸣ }
  Transitive[≈♮] : ∀ {ℓ} {A : Poset ℓ} → Transitive (_≈♮_ {A = A})
  Transitive[≈♮] = record { _⊚_ = _⊚⸢≈♮⸣_ }
  Symmetric[≈♮] : ∀ {ℓ} {A : Poset ℓ} → Symmetric (_≈♮_ {A = A})
  Symmetric[≈♮] = record { ◇ = ◇⸢≈♮⸣ }
  Precision[Poset] : ∀ {ℓ} {A : Poset ℓ} → Precision ℓ ⟪ A ⟫
  Precision[Poset] = mk[Precision] _⊑♮_

intro[⊑♮] : ∀ {ℓ} {A : Set ℓ} {{_ : Precision ℓ  A}} {x y : A} → x ⊑ y → ♮ x ⊑♮ ♮ y
intro[⊑♮] = ♮⟨_⟩

elim[⊑♮] : ∀ {ℓ} {A : Set ℓ} {{_ : Precision ℓ A}} {x y : A} → ♮ x ⊑♮ ♮ y → x ⊑ y
elim[⊑♮] ♮⟨ x≼y ⟩ = x≼y

intro[⊑♭] : ∀ {ℓ} {A : Set ℓ} {{_ : Precision ℓ A}} {x y : ⟪ ⇧ A ⟫} → ♭ x ⊑ ♭ y → x ⊑♮ y
intro[⊑♭] {x = ♮⟨ x ⟩} {y = ♮⟨ y ⟩} x≼y = ♮⟨ x≼y ⟩

elim[⊑♭] : ∀ {ℓ} {A : Set ℓ} {{_ : Precision ℓ A}} {x y : ⟪ ⇧ A ⟫} → x ⊑♮ y → ♭ x ⊑ ♭ y
elim[⊑♭] ♮⟨ x≼y ⟩ = x≼y
