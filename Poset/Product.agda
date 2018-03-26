module Poset.Product where

open import Prelude
open import Poset.Poset
open import Poset.Fun

infixr 13 _∧♮_
infix  14 _≼⸢∧♭⸣_
infixr 30 _⊚⸢≼∧♭⸣_

data _∧♭_ {ℓ₁ ℓ₂} (A : Poset ℓ₁) (B : Poset ℓ₂) : Set (ℓ₁ ⊔ᴸ ℓ₂) where
  ⟨_,_⟩ : ⟪ A ⟫ → ⟪ B ⟫ → A ∧♭ B

π₁⸢∧♭⸣ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → A ∧♭ B → ⟪ A ⟫
π₁⸢∧♭⸣ ⟨ x , _ ⟩ = x

π₂⸢∧♭⸣ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → A ∧♭ B → ⟪ B ⟫
π₂⸢∧♭⸣ ⟨ _ , y ⟩ = y

data _≼⸢∧♭⸣_ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} : relation (ℓ₁ ⊔ᴸ ℓ₂) (A ∧♭ B) where
  ⟨_,_⟩ : ∀ {x₁ x₂ y₁ y₂} → x₁ ⊑♮ x₂ → y₁ ⊑♮ y₂ → ⟨ x₁ , y₁ ⟩ ≼⸢∧♭⸣ ⟨ x₂ , y₂ ⟩

xRx⸢≼∧♭⸣ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → reflexive (_≼⸢∧♭⸣_ {A = A} {B})
xRx⸢≼∧♭⸣ {x = ⟨ x , y ⟩} = ⟨ xRx , xRx ⟩

_⊚⸢≼∧♭⸣_ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → transitive (_≼⸢∧♭⸣_ {A = A} {B})
⟨ x₂⊑x₃ , y₂⊑y₃ ⟩ ⊚⸢≼∧♭⸣ ⟨ x₁⊑x₂ , y₁⊑y₂ ⟩ = ⟨ x₂⊑x₃ ⊚ x₁⊑x₂ , y₂⊑y₃ ⊚ y₁⊑y₂ ⟩

instance
  Reflexive[≼⸢∧♭⸣] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → Reflexive (_≼⸢∧♭⸣_ {A = A} {B})
  Reflexive[≼⸢∧♭⸣] = record { xRx = xRx⸢≼∧♭⸣ }
  Transitive[≼⸢∧♭⸣] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → Transitive (_≼⸢∧♭⸣_ {A = A} {B})
  Transitive[≼⸢∧♭⸣] = record { _⊚_ = _⊚⸢≼∧♭⸣_ }
  Precision[∧♭] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → Precision (ℓ₁ ⊔ᴸ ℓ₂) (A ∧♭ B)
  Precision[∧♭] = mk[Precision] _≼⸢∧♭⸣_

_∧♮_ : ∀ {ℓ₁ ℓ₂} → Poset ℓ₁ → Poset ℓ₂ → Poset (ℓ₁ ⊔ᴸ ℓ₂)
A ∧♮ B = ⇧ (A ∧♭ B)

_∧ʷ_ : ∀ {ℓ₁ ℓ₂ ℓ₁ʳ ℓ₂ʳ} {A : Set ℓ₁} {B : Set ℓ₂} (_R₁_ : relation ℓ₁ʳ A) (_R₂_ : relation ℓ₂ʳ B) → relation (ℓ₁ʳ ⊔ᴸ ℓ₂ʳ) (A ∧ B)
(_R₁_ ∧ʷ _R₂_) ⟨ x₁ , y₁ ⟩ ⟨ x₂ , y₂ ⟩ = (x₁ R₁ x₂) ∧ (y₁ R₂ y₂)

module _ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ} {A : Set ℓ₁} {B : Set ℓ₂} {_R₁_ : relation ℓ₁ʳ A} {_R₂_ : relation ℓ₂ʳ B} {{REX₁ : Reflexive _R₁_}} {{REX₂ : Reflexive _R₂_}} where
  Reflexive[∧ʷ] : Reflexive (_R₁_ ∧ʷ _R₂_)
  Reflexive[∧ʷ] = record { xRx = ⟨ xRx {{REX₁}} , xRx {{REX₂}} ⟩}

module _ {ℓ₁₁ ℓ₂₁ ℓ₁₂ ℓ₂₂} {A₁ : Poset ℓ₁₁} {A₂ : Poset ℓ₂₁} {B₁ : Set ℓ₁₂} {B₂ : Set ℓ₂₂} {{_ : Precision ℓ₁₂ B₁}} {{_ : Precision ℓ₂₂ B₂}} where
  _<∧♭>_ : ⟪ _⊑♮_ {A = A₁} ⇉ʷ _⊑_ {A = B₁} ⟫ʷ → ⟪ _⊑♮_ {A = A₂} ⇉ʷ _⊑_ {A = B₂} ⟫ʷ → ⟪ _⊑♮_ {A = A₁ ∧♮ A₂} ⇉ʷ _⊑_ {A = B₁} ∧ʷ _⊑_ {A = B₂}⟫ʷ
  f <∧♭> g = mk[witness] F proper[F]
    where
      F : ⟪ _⊑♮_ {A = A₁ ∧♮ A₂} ⟫ʷ → B₁ ∧ B₂
      F (mk[witness] ♮⟨ ⟨ x , y ⟩ ⟩ ♮⟨ ⟨ proper[x] , proper[y] ⟩ ⟩) = ⟨ witness f (mk[witness] x proper[x]) , witness g (mk[witness] y proper[y]) ⟩
      proper[F] : proper (_⊑♮_ {A = A₁ ∧♮ A₂} ⇉ʷ _⊑_ {A = B₁} ∧ʷ _⊑_ {A = B₂}) F
      proper[F] {mk[witness] ♮⟨ ⟨ x₁ , y₁ ⟩ ⟩ ♮⟨ ⟨ proper[x₁] , proper[y₁] ⟩ ⟩} {mk[witness] ♮⟨ ⟨ x₂ , y₂ ⟩ ⟩ ♮⟨ ⟨ proper[x₂] , proper[y₂] ⟩ ⟩} ♮⟨ ⟨ x₁≼x₂ , y₁≼y₂ ⟩ ⟩ =
        ⟨ proper[witness] f x₁≼x₂ , proper[witness] g y₁≼y₂ ⟩
  _<∧♮>_ : ⟪ _⊑_ {A = B₁} ⇉ʷ _⊑♮_ {A = A₁} ⟫ʷ → ⟪ _⊑_ {A = B₂} ⇉ʷ _⊑♮_ {A = A₂} ⟫ʷ → ⟪ _⊑_ {A = B₁} ∧ʷ _⊑_ {A = B₂} ⇉ʷ _⊑♮_ {A = A₁ ∧♮ A₂} ⟫ʷ
  f <∧♮> g = mk[witness] F proper[F]
    where
      F : ⟪ _⊑_ {A = B₁} ∧ʷ _⊑_ {A = B₂} ⟫ʷ → ⟪ A₁ ∧♮ A₂ ⟫
      F (mk[witness] ⟨ x , y ⟩ ⟨ proper[x] , proper[y] ⟩) = ♮⟨ ⟨ witness f (mk[witness] x proper[x]) , witness g (mk[witness] y proper[y]) ⟩ ⟩
      proper[F] : proper (_⊑_ {A = B₁} ∧ʷ _⊑_ {A = B₂} ⇉ʷ _⊑♮_ {A = A₁ ∧♮ A₂}) F
      proper[F] {mk[witness] ⟨ x₁ , y₁ ⟩ ⟨ proper[x₁] , proper[y₁] ⟩} {mk[witness] ⟨ x₂ , y₂ ⟩ ⟨ proper[x₂] , proper[y₂] ⟩} ⟨ x₁Rx₂ , y₁Ry₂ ⟩ =
        ♮⟨ ⟨ proper[witness] f x₁Rx₂ , proper[witness] g y₁Ry₂ ⟩ ⟩

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₃ʳ ℓ₄} {A₁ : Set ℓ₁} {{_ : Precision ℓ₁ A₁}} {A₂ : Set ℓ₂} {{_ : Precision ℓ₂ A₂}} {B : Set ℓ₃} {_R_ : relation ℓ₃ʳ B} {C : Poset ℓ₄} where
  curry⸢λ♭∧♭⸣ : ⟪ _R_ ⇉ʷ _⊑♮_ {A = C} ⟫ʷ → ⟪ (_⊑_ {A = A₁} ∧ʷ _⊑_ {A = A₂} ⇉ _R_) ⇉ʷ _⊑♮_ {A = (⇧ A₁) ∧♮ (⇧ A₂) ↗ C} ⟫ʷ
  curry⸢λ♭∧♭⸣ = curry⸢λ⸣[ <♭> <∧♭> <♭> ] {{Reflexive[∧ʷ] {{Reflexive[⊑]}} {{Reflexive[⊑]}}}}
  id⸢λ♭∧♭⸣ : ⟪ _⊑_ {A = A₁} ∧ʷ _⊑_ {A = A₂} ⇉ʷ _⊑♮_ {A = (⇧ A₁) ∧♮ (⇧ A₂)} ⟫ʷ
  id⸢λ♭∧♭⸣ = <♮> <∧♮> <♮>

[,] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → ⟪ A ↗ B ↗ A ∧♮ B ⟫
[,] {ℓ₁} {ℓ₂} {A = A} {B} = witness (curry⸢λ⸣ $ curry⸢λ⸣ {ℓ₂ʳ = ℓ₁ ⊔ᴸ ℓ₂} id⸢λ♭⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ B ⟫ → A ∧♭ B
    fun = ⟨_,_⟩
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_ ⇉ _⊑_) fun
      ppr x₁⊑x₂ y₁⊑y₂ = ⟨ x₁⊑x₂ , y₁⊑y₂ ⟩

⟨_,♮_⟩ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → ⟪ A ⟫ → ⟪ B ⟫ → ⟪ A ∧♮ B ⟫
⟨ x ,♮ y ⟩ = [,] ⋅ x ⋅ y

π₁♮ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → ⟪ A ∧♮ B ↗ A ⟫
π₁♮ {A = A} {B} = witness (curry⸢λ♭⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : A ∧♭ B → ⟪ A ⟫
    fun ⟨ x , _ ⟩ = x
    abstract
      ppr : proper (_⊑_ ⇉ _⊑♮_) fun
      ppr ⟨ x₁⊑x₂ , _ ⟩ = x₁⊑x₂

π₂♮ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → ⟪ A ∧♮ B ↗ B ⟫
π₂♮ {A = A} {B} = witness (curry⸢λ♭⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : A ∧♭ B → ⟪ B ⟫
    fun ⟨ _ , y ⟩ = y
    abstract
      ppr : proper (_⊑_ ⇉ _⊑♮_) fun
      ppr ⟨ _ , y₁⊑y₂ ⟩ = y₁⊑y₂
