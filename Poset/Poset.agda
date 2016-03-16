module Poset.Poset where

open import Prelude

infixr 3 _,_
infix 14 _⊑♮_
infix 14 _⊒♮_
infix 14 _≈♮_
infixr 30 _⊚⸢⊑♮⸣_
infixr 30 _⊚⸢≈♮⸣_

data Poset ℓ : Set (↑ᴸ ℓ) where
  ⇧ : (A : Set ℓ) → {{A-PO : PreOrder ℓ A}} → Poset ℓ

dom : ∀ {ℓ} → Poset ℓ → Set ℓ
dom (⇧ A) = A

[_]_≼⸢dom⸣_ : ∀ {ℓ} (A : Poset ℓ) → relation ℓ (dom A)
[ ⇧ A ] x ≼⸢dom⸣ y = x ≼ y

data ⟪_⟫ {ℓ} (A : Poset ℓ) : Set ℓ where
  ♮⟨_⟩ : dom A → ⟪ A ⟫

♮ : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} → A → ⟪ ⇧ A ⟫
♮ = ♮⟨_⟩

♭ : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} → ⟪ ⇧ A ⟫ → A
♭ (♮⟨ A ⟩) = A

data _⊑♮_ {ℓ} {A : Poset ℓ} : relation ℓ ⟪ A ⟫ where
  ♮⟨_⟩ : {x y : dom A} → [ A ] x ≼⸢dom⸣ y → ♮⟨ x ⟩ ⊑♮ ♮⟨ y ⟩

_⊒♮_ : ∀ {ℓ} {A : Poset ℓ} → relation ℓ ⟪ A ⟫
_⊒♮_ = flip _⊑♮_

data _≈♮_ {ℓ} {A : Poset ℓ} : relation ℓ ⟪ A ⟫ where
  _,_ : ∀ {x y} → x ⊑♮ y → y ⊑♮ x → x ≈♮ y

xRx⸢⊑♮⸣ : ∀ {ℓ} {A : Poset ℓ} → reflexive (_⊑♮_ {A = A})
xRx⸢⊑♮⸣ {A = ⇧ A {{A-PO}}} {x = ♮⟨ x ⟩} = ♮⟨ xRx⸢≼⸣ {{A-PO}}⟩

_⊚⸢⊑♮⸣_ : ∀ {ℓ} {A : Poset ℓ} → transitive (_⊑♮_ {A = A})
_⊚⸢⊑♮⸣_ {A = ⇧ A {{A-PO}}} ♮⟨ y≼z ⟩ ♮⟨ x≼y ⟩ = ♮⟨ _⊚⸢≼⸣_ {{A-PO}} y≼z x≼y ⟩

xRx[≈]⸢⊑♮⸣ : ∀ {ℓ} {A : Poset ℓ} → reflexive[ _≈♮_ ] (_⊑♮_ {A = A})
xRx[≈]⸢⊑♮⸣ (x⊑y , _) = x⊑y

⋈[≈]⸢⊑♮⸣ : ∀ {ℓ} {A : Poset ℓ} → antisymmetric[ _≈♮_ ] (_⊑♮_ {A = A})
⋈[≈]⸢⊑♮⸣ = _,_

xRx⸢≈♮⸣ : ∀ {ℓ} {A : Poset ℓ} → reflexive (_≈♮_ {A = A})
xRx⸢≈♮⸣ = xRx⸢⊑♮⸣ , xRx⸢⊑♮⸣

_⊚⸢≈♮⸣_ : ∀ {ℓ} {A : Poset ℓ} → transitive (_≈♮_ {A = A})
(y⊑z , z⊑y) ⊚⸢≈♮⸣ (x⊑y , y⊑x) = y⊑z ⊚⸢⊑♮⸣ x⊑y , y⊑x ⊚⸢⊑♮⸣ z⊑y

◇⸢≈♮⸣ : ∀ {ℓ} {A : Poset ℓ} → symmetric (_≈♮_ {A = A})
◇⸢≈♮⸣ (x⊑y , y⊑x) = y⊑x , x⊑y

instance
  Reflexive[⊑♮] : ∀ {ℓ} {A : Poset ℓ} → Reflexive (_⊑♮_ {A = A})
  Reflexive[⊑♮] = record { xRx = xRx⸢⊑♮⸣ }
  Transitive[⊑♮] : ∀ {ℓ} {A : Poset ℓ} → Transitive (_⊑♮_ {A = A})
  Transitive[⊑♮] = record { _⊚_ = _⊚⸢⊑♮⸣_ }
  Reflexive[≈][⊑♮] : ∀ {ℓ} {A : Poset ℓ} → Reflexive[ _≈♮_ ] (_⊑♮_ {A = A})
  Reflexive[≈][⊑♮] = record { xRx[] = xRx[≈]⸢⊑♮⸣ }
  Antisymmetric[≈][⊑♮] : ∀ {ℓ} {A : Poset ℓ} → Antisymmetric[ _≈♮_ ] (_⊑♮_ {A = A})
  Antisymmetric[≈][⊑♮] = record { ⋈[] = ⋈[≈]⸢⊑♮⸣ }
  Reflexive[≈♮] : ∀ {ℓ} {A : Poset ℓ} → Reflexive (_≈♮_ {A = A})
  Reflexive[≈♮] = record { xRx = xRx⸢≈♮⸣ }
  Transitive[≈♮] : ∀ {ℓ} {A : Poset ℓ} → Transitive (_≈♮_ {A = A})
  Transitive[≈♮] = record { _⊚_ = _⊚⸢≈♮⸣_ }
  Symmetric[≈♮] : ∀ {ℓ} {A : Poset ℓ} → Symmetric (_≈♮_ {A = A})
  Symmetric[≈♮] = record { ◇ = ◇⸢≈♮⸣ }

intro[⊑♮] : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ  A}} {x y : A} → x ≼ y → ♮ x ⊑♮ ♮ y
intro[⊑♮] = ♮⟨_⟩

elim[⊑♮] : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} {x y : A} → ♮ x ⊑♮ ♮ y → x ≼ y
elim[⊑♮] ♮⟨ x≼y ⟩ = x≼y

intro[⊑♭] : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} {x y : ⟪ ⇧ A ⟫} → ♭ x ≼ ♭ y → x ⊑♮ y
intro[⊑♭] {x = ♮⟨ x ⟩} {y = ♮⟨ y ⟩} x≼y = ♮⟨ x≼y ⟩

elim[⊑♭] : ∀ {ℓ} {A : Set ℓ} {{PO : PreOrder ℓ A}} {x y : ⟪ ⇧ A ⟫} → x ⊑♮ y → ♭ x ≼ ♭ y
elim[⊑♭] ♮⟨ x≼y ⟩ = x≼y
