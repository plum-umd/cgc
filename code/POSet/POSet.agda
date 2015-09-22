module POSet.POSet where

open import Prelude

data POSet 𝓁 : Set (sucˡ 𝓁) where
  ⇧ : (A : Set 𝓁) → {{A-PO : PreOrder 𝓁 A}} → POSet 𝓁

dom : ∀ {𝓁} → POSet 𝓁 → Set 𝓁
dom (⇧ A) = A

[_]_⊴⸢dom⸣_ : ∀ {𝓁} (A : POSet 𝓁) → relation 𝓁 (dom A)
[ ⇧ A ] x ⊴⸢dom⸣ y = x ⊴ y

-- ⇧-A-PO : ∀ {𝓁} → (A : POSet 𝓁) → PreOrder 𝓁 (⇧-A A)
-- ⇧-A-PO (⇧ A {{A-PO}}) = A-PO
  
data ⟪_⟫ {𝓁} (A : POSet 𝓁) : Set 𝓁 where
  ↑⟨_⟩ : dom A → ⟪ A ⟫

↑ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} → A → ⟪ ⇧ A ⟫
↑ = ↑⟨_⟩

↓ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} → ⟪ ⇧ A ⟫ → A
↓ (↑⟨ A ⟩) = A

-- res[≡]⸢↑⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : A} → x ≡ y → ↑ x ≡ ↑ y
-- res[≡]⸢↑⸣ ↯ = ↯
-- 
-- inj[≡]⸢↑⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : A} → ↑ x ≡ ↑ y → x ≡ y
-- inj[≡]⸢↑⸣ ↯ = ↯
-- 
-- res[≡]⸢↓⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : ⟪ ⇧ A ⟫} → x ≡ y → ↓ x ≡ ↓ y
-- res[≡]⸢↓⸣ ↯ = ↯
-- 
-- inj[≡]⸢↓⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : ⟪ ⇧ A ⟫} → ↓ x ≡ ↓ y → x ≡ y
-- inj[≡]⸢↓⸣ {x = ↑⟨ x ⟩} {↑⟨ .x ⟩} ↯ = ↯

infix 8 _⊑_
data _⊑_ {𝓁} {A : POSet 𝓁} : relation 𝓁 ⟪ A ⟫ where
  ↑⟨_⟩ : {x y : dom A} → [ A ] x ⊴⸢dom⸣ y → ↑⟨ x ⟩ ⊑ ↑⟨ y ⟩

infix 8 _⊒_
_⊒_ : ∀ {𝓁} {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫
_⊒_ = flip _⊑_

infix 8 _≈_
infixr 3 _,_
data _≈_ {𝓁} {A : POSet 𝓁} : relation 𝓁 ⟪ A ⟫ where
  _,_ : ∀ {x y} → x ⊑ y → y ⊑ x → x ≈ y

xRx⸢⊑⸣ : ∀ {𝓁} {A : POSet 𝓁} → reflexive (_⊑_ {A = A})
xRx⸢⊑⸣ {A = ⇧ A} {x = ↑⟨ x ⟩} = ↑⟨ xRx⸢⊴⸣ ⟩

infixr 9 _⌾⸢⊑⸣_
_⌾⸢⊑⸣_ : ∀ {𝓁} {A : POSet 𝓁} → transitive (_⊑_ {A = A})
_⌾⸢⊑⸣_ {A = ⇧ A} ↑⟨ y⊴z ⟩ ↑⟨ x⊴y ⟩ = ↑⟨ y⊴z ⌾⸢⊴⸣ x⊴y ⟩

xRx[≈]⸢⊑⸣ : ∀ {𝓁} {A : POSet 𝓁} → reflexive[ _≈_ ] (_⊑_ {A = A})
xRx[≈]⸢⊑⸣ (x⊑y , _) = x⊑y

⋈[≈]⸢⊑⸣ : ∀ {𝓁} {A : POSet 𝓁} → antisymmetric[ _≈_ ] (_⊑_ {A = A})
⋈[≈]⸢⊑⸣ = _,_

xRx⸢≈⸣ : ∀ {𝓁} {A : POSet 𝓁} → reflexive (_≈_ {A = A})
xRx⸢≈⸣ = xRx⸢⊑⸣ , xRx⸢⊑⸣

infixr 9 _⌾⸢≈⸣_
_⌾⸢≈⸣_ : ∀ {𝓁} {A : POSet 𝓁} → transitive (_≈_ {A = A})
(y⊑z , z⊑y) ⌾⸢≈⸣ (x⊑y , y⊑x) = y⊑z ⌾⸢⊑⸣ x⊑y , y⊑x ⌾⸢⊑⸣ z⊑y

◇⸢≈⸣ : ∀ {𝓁} {A : POSet 𝓁} → symmetric (_≈_ {A = A})
◇⸢≈⸣ (x⊑y , y⊑x) = y⊑x , x⊑y

instance
  Reflexive[⊑] : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_⊑_ {A = A})
  Reflexive[⊑] = record { xRx = xRx⸢⊑⸣ }
  Transitive[⊑] : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_⊑_ {A = A})
  Transitive[⊑] = record { _⌾_ = _⌾⸢⊑⸣_ }
  Reflexive[≈][⊑] : ∀ {𝓁} {A : POSet 𝓁} → Reflexive[ _≈_ ] (_⊑_ {A = A})
  Reflexive[≈][⊑] = record { xRx[] = xRx[≈]⸢⊑⸣ }
  Antisymmetric[≈][⊑] : ∀ {𝓁} {A : POSet 𝓁} → Antisymmetric[ _≈_ ] (_⊑_ {A = A})
  Antisymmetric[≈][⊑] = record { ⋈[] = ⋈[≈]⸢⊑⸣ }
  Reflexive[≈] : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_≈_ {A = A})
  Reflexive[≈] = record { xRx = xRx⸢≈⸣ }
  Transitive[≈] : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_≈_ {A = A})
  Transitive[≈] = record { _⌾_ = _⌾⸢≈⸣_ }
  Symmetric[≈] : ∀ {𝓁} {A : POSet 𝓁} → Symmetric (_≈_ {A = A})
  Symmetric[≈] = record { ◇ = ◇⸢≈⸣ }

intro[⊑]⸢↑⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁  A}} {x y : A} → x ⊴ y → ↑ x ⊑ ↑ y
intro[⊑]⸢↑⸣ = ↑⟨_⟩

elim[⊑]⸢↑⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : A} → ↑ x ⊑ ↑ y → x ⊴ y
elim[⊑]⸢↑⸣ ↑⟨ x⊴y ⟩ = x⊴y

intro[⊑]⸢↓⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : ⟪ ⇧ A ⟫} → ↓ x ⊴ ↓ y → x ⊑ y
intro[⊑]⸢↓⸣ {x = ↑⟨ x ⟩} {y = ↑⟨ y ⟩} x⊴y = ↑⟨ x⊴y ⟩

elim[⊑]⸢↓⸣ : ∀ {𝓁} {A : Set 𝓁} {{PO : PreOrder 𝓁 A}} {x y : ⟪ ⇧ A ⟫} → x ⊑ y → ↓ x ⊴ ↓ y
elim[⊑]⸢↓⸣ ↑⟨ x⊴y ⟩ = x⊴y
