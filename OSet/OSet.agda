module OSet.OSet where

open import Prelude

data POSet 𝓁 : Set (sucˡ 𝓁) where
  ⇧ : (A : Set 𝓁) → {{A-PO : PreOrder 𝓁 A}} → POSet 𝓁

⇧-A : ∀ {𝓁} → POSet 𝓁 → Set 𝓁
⇧-A (⇧ A) = A

⇧-A-PO : ∀ {𝓁} → (A : POSet 𝓁) → PreOrder 𝓁 (⇧-A A)
⇧-A-PO (⇧ A {{A-PO}}) = A-PO
  
data ⟪_⟫ {𝓁} (A : POSet 𝓁) : Set 𝓁 where
  ↑⟨_⟩ : ⇧-A A → ⟪ A ⟫

↑ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} → A → ⟪ ⇧ A ⟫
↑ = ↑⟨_⟩

↓ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} → ⟪ ⇧ A ⟫ → A
↓ (↑⟨ A ⟩) = A

res[≡]⸢↑⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : A} → x ≡ y → ↑ x ≡ ↑ y
res[≡]⸢↑⸣ ↯ = ↯

inj[≡]⸢↑⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : A} → ↑ x ≡ ↑ y → x ≡ y
inj[≡]⸢↑⸣ ↯ = ↯

res[≡]⸢↓⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : ⟪ ⇧ A ⟫} → x ≡ y → ↓ x ≡ ↓ y
res[≡]⸢↓⸣ ↯ = ↯

inj[≡]⸢↓⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : ⟪ ⇧ A ⟫} → ↓ x ≡ ↓ y → x ≡ y
inj[≡]⸢↓⸣ {x = ↑⟨ x ⟩} {↑⟨ .x ⟩} ↯ = ↯

data _⊴⸢⟪⟫⸣_ {𝓁} {A : POSet 𝓁} : relation 𝓁 ⟪ A ⟫ where
  ↑⟨_⟩ : {x y : ⇧-A A} → _⊴_ {{⇧-A-PO A}} x y → ↑⟨ x ⟩ ⊴⸢⟪⟫⸣ ↑⟨ y ⟩

xRx⸢⊴⸢⟪⟫⸣⸣ : ∀ {𝓁} {A : POSet 𝓁} → reflexive (_⊴⸢⟪⟫⸣_ {A = A})
xRx⸢⊴⸢⟪⟫⸣⸣ {A = ⇧ A} {x = ↑⟨ x ⟩} = ↑⟨ xRx⸢⊴⸣ ⟩

_⌾⸢⊴⸢⟪⟫⸣⸣_ : ∀ {𝓁} {A : POSet 𝓁} → transitive (_⊴⸢⟪⟫⸣_ {A = A})
_⌾⸢⊴⸢⟪⟫⸣⸣_ {A = ⇧ A} ↑⟨ y⊴z ⟩ ↑⟨ x⊴y ⟩ = ↑⟨ y⊴z ⌾⸢⊴⸣ x⊴y ⟩

instance
  Reflexive[⊴⸢⟪⟫⸣] : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_⊴⸢⟪⟫⸣_ {A = A})
  Reflexive[⊴⸢⟪⟫⸣] = record { xRx = xRx⸢⊴⸢⟪⟫⸣⸣ }
  Transitive[⊴⸢⟪⟫⸣] : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_⊴⸢⟪⟫⸣_ {A = A})
  Transitive[⊴⸢⟪⟫⸣] = record { _⌾_ = _⌾⸢⊴⸢⟪⟫⸣⸣_ }
  PreOrder[⟪⟫] : ∀ {𝓁} {A : POSet 𝓁} → PreOrder 𝓁 ⟪ A ⟫
  PreOrder[⟪⟫] = record { _⊴_ = _⊴⸢⟪⟫⸣_ }
  PartialOrder[⟪⟫] : ∀ {𝓁} {A : POSet 𝓁} → PartialOrder 𝓁 ⟪ A ⟫ _⊴⊵_
  PartialOrder[⟪⟫] = ⊴⊵-PartialOrder
  Equivalence[⟪⟫] : ∀ {𝓁} {A : POSet 𝓁} → Equivalence 𝓁 ⟪ A ⟫
  Equivalence[⟪⟫] = ⊴⊵-Equivalence

intro[⊑]⸢↑⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁  A}} {x y : A} → x ⊴ y → ↑ x ⊑ ↑ y
intro[⊑]⸢↑⸣ = ↑⟨_⟩

elim[⊑]⸢↑⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : A} → ↑ x ⊑ ↑ y → x ⊴ y
elim[⊑]⸢↑⸣ ↑⟨ x⊴y ⟩ = x⊴y

intro[⊑]⸢↓⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : ⟪ ⇧ A ⟫} → ↓ x ⊴ ↓ y → x ⊑ y
intro[⊑]⸢↓⸣ {x = ↑⟨ x ⟩} {y = ↑⟨ y ⟩} x⊴y = ↑⟨ x⊴y ⟩

elim[⊑]⸢↓⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : ⟪ ⇧ A ⟫} → x ⊑ y → ↓ x ⊴ ↓ y
elim[⊑]⸢↓⸣ ↑⟨ x⊴y ⟩ = x⊴y
