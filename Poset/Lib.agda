module Poset.Lib where

open import Prelude
open import Poset.Poset
open import Poset.Fun
open import Poset.Power
open import Poset.Product
open import Poset.Classes
open import Poset.List

infixr 30 _∘♮_

id♮ : ∀ {ℓ} {A : Poset ℓ} → ⟪ A ↗ A ⟫
id♮ = witness (curry⸢λ⸣ id⸢λ⸣) $ mk[witness] id id

_∘♮_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} → ⟪ B ↗ C ⟫ → ⟪ A ↗ B ⟫ → ⟪ A ↗ C ⟫
_∘♮_ {A = A} {B} {C} g f = witness (curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ C ⟫
    fun x = g ⋅ (f ⋅ x)
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_) fun
      ppr x⊑y = res[•x][↗]⸢⊑⸣ {f = g} (res[•x][↗]⸢⊑⸣ {f = f} x⊑y)

[∘♮] : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} → ⟪ (B ↗ C) ↗ (A ↗ B) ↗ (A ↗ C) ⟫
[∘♮] {A = A} {B} {C} = witness (curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ B ↗ C ⟫ → ⟪ A ↗ B ⟫ → ⟪ A ↗ C ⟫
    fun g f = g ∘♮ f
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_) fun
      ppr {g₁} {g₂} g₁⊑g₂ {f₁} {f₂} f₁⊑f₂ = ext[↗]⸢⊑⸣ (res[fx][↗]⸢⊑⸣ g₁⊑g₂ (res[f•][↗]⸢⊑⸣ f₁⊑f₂))

right-unit[∘♮] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} {f : ⟪ A ↗ B ⟫} → f ∘♮ id♮ ≈♮ f
right-unit[∘♮] = ext[↗]⸢≈⸣ xRx

associative[∘♮] : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} {D : Poset ℓ₄} {h : ⟪ C ↗ D ⟫} {g : ⟪ B ↗ C ⟫} {f : ⟪ A ↗ B ⟫} → (h ∘♮ g) ∘♮ f ≈♮ h ∘♮ (g ∘♮ f)
associative[∘♮] = ext[↗]⸢≈⸣ xRx

wrap : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} {D : Poset ℓ₄} → ⟪ (C ↗ D) ↗ (A ↗ B) ↗ (B ↗ C) ↗ A ↗ D ⟫
wrap {A = A} {B} {C} {D} = witness (curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ C ↗ D ⟫ → ⟪ A ↗ B ⟫ → ⟪ B ↗ C ⟫ → ⟪ A ↗ D ⟫
    fun h f g = h ∘♮ g ∘♮ f
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_) fun
      ppr h₁⊑h₂ f₁⊑f₂ g₁⊑g₂ = ext[↗]⸢⊑⸣ $ λ {x} → res[fx][↗]⸢⊑⸣ h₁⊑h₂ (res[fx][↗]⸢⊑⸣ g₁⊑g₂ (res[f•][↗]⸢⊑⸣ f₁⊑f₂))

[⋅] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → ⟪ (A ↗ B) ↗ A ↗ B ⟫
[⋅] {A = A} {B} = witness (curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ↗ B ⟫ → ⟪ A ⟫ → ⟪ B ⟫
    fun = _⋅_
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_) fun
      ppr f⊑g x⊑y = res[fx][↗]⸢⊑⸣ f⊑g x⊑y

const♮ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → ⟪ A ↗ B ↗ A ⟫
const♮ {A = A} {B} = witness (curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ B ⟫ → ⟪ A ⟫
    fun = const
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_) fun
      ppr x⊑y _ = x⊑y

uncurry♮ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} → ⟪ (A ↗ B ↗ C) ↗ A ∧♮ B ↗ C ⟫
uncurry♮ {A = A} {B} {C} = witness (curry⸢λ⸣ $ curry⸢λ♭⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ↗ B ↗ C ⟫ → A ∧♭ B → ⟪ C ⟫
    fun f ⟨ x , y ⟩ = f ⋅ x ⋅ y
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑_ ⇉ _⊑♮_) fun
      ppr f⊑g ⟨ x₁⊑x₂ , y₁⊑y₂ ⟩ = res[fx][↗]⸢⊑⸣ (res[fx][↗]⸢⊑⸣ f⊑g x₁⊑x₂) y₁⊑y₂

flip♮ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} → ⟪ (A ↗ B ↗ C) ↗ B ↗ A ↗ C ⟫
flip♮ {A = A} {B} {C} = witness (curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ↗ B ↗ C ⟫ → ⟪ B ⟫ → ⟪ A ⟫ → ⟪ C ⟫
    fun f y x = f ⋅ x ⋅ y
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_) fun
      ppr f₁⊑f₂ x₁⊑x₂ y₁⊑y₂ = res[fx][↗]⸢⊑⸣ (res[fx][↗]⸢⊑⸣ f₁⊑f₂ y₁⊑y₂) x₁⊑x₂

split♮ : ∀ {ℓ} {A : Poset ℓ} → ⟪ A ↗ A ∧♮ A ⟫
split♮ {A = A} = witness (curry⸢λ⸣ id⸢λ♭⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → A ∧♭ A
    fun x = ⟨ x , x ⟩
    abstract
      ppr : proper (_⊑♮_ ⇉ _⊑_) fun
      ppr x⊑y = ⟨ x⊑y , x⊑y ⟩

apply♮ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} → ⟪ (A ↗ B) ∧♮ A ↗ B ⟫
apply♮ {A = A} {B} = witness (curry⸢λ♭⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : (A ↗ B) ∧♭ A → ⟪ B ⟫
    fun ⟨ f , x ⟩ = f ⋅ x
    ppr : proper (_⊑_ ⇉ _⊑♮_) fun
    ppr ⟨ ⊑ᶠ , ⊑ᶻ ⟩ = res[fx][↗]⸢⊑⸣ ⊑ᶠ ⊑ᶻ

apply⸢∧♮⸣ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} {D : Poset ℓ₄} → ⟪ (A ↗ B) ∧♮ (C ↗ D) ↗ A ∧♮ C ↗ B ∧♮ D ⟫
apply⸢∧♮⸣ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} {A} {B} {C} {D} = witness (curry⸢λ♭⸣ $ curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] fun ppr
  where
    fun : (A ↗ B) ∧♭ (C ↗ D) → A ∧♭ C → B ∧♭ D
    fun ⟨ f , g ⟩ ⟨ x , y ⟩ = ⟨ f ⋅ x , g ⋅ y ⟩
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr ⟨ f₁⊑f₂ , g₁⊑g₂ ⟩ ⟨ x₁⊑x₂ , y₁⊑y₂ ⟩ = ⟨ res[fx][↗]⸢⊑⸣ f₁⊑f₂ x₁⊑x₂ , res[fx][↗]⸢⊑⸣ g₁⊑g₂ y₁⊑y₂ ⟩
  
all♮ : ∀ {ℓ} (A : Poset ℓ) → ⟪ ℘ A ⟫
all♮ {ℓ} A = witness id⸢ω⸣ $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → Set ℓ
    fun = const $ lift ℓ unit
    abstract
      ppr : proper (_⊒♮_ {A = A} ⇉ [→]) fun
      ppr = const id

all♮-in : ∀ {ℓ} {A : Poset ℓ} {x : ⟪ A ⟫} → x ⋿ all♮ A
all♮-in = mk[lift] tt

empty♮ : ∀ {ℓ} {A : Poset ℓ} → ⟪ ℘ A ⟫
empty♮ {ℓ} {A} = witness id⸢ω⸣ $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → Set ℓ
    fun = const $ lift ℓ void
    abstract
      ppr : proper (_⊑♮_ ⇉ [→]) fun
      ppr _ (mk[lift] ())

single♮ : ∀ {ℓ} {A : Poset ℓ} → ⟪ A ↗ list♮ A ⟫
single♮ {A = A} = witness (curry⸢λ⸣ id⸢λ♭⸣) $ mk[witness] singleˡ♭ mon[single]ˡ♭

[⧺] : ∀ {ℓ} {A : Poset ℓ} → ⟪ list♮ A ↗ list♮ A ↗ list♮ A ⟫
[⧺] {A = A} = witness (curry⸢λ♭⸣ $ curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] _⧺ˡ♭_ mon[⧺]ˡ♭

module _ {ℓ} {A : Poset ℓ} where
  []♮ : ⟪ list♮ A ⟫
  []♮ = ♮⟨ [] ⟩
  
  _⧺♮_ : ⟪ list♮ A ⟫ → ⟪ list♮ A ⟫ → ⟪ list♮ A ⟫
  xs ⧺♮ ys = [⧺] ⋅ xs ⋅ ys

  join[]♮ : ⟪ list♮ (list♮ A) ↗ list♮ A ⟫
  join[]♮ = witness (curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] join[]♭ mon[join[]♭]

module _ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} where
  map[]♮ : ⟪ (A ↗ B) ↗ list♮ A ↗ list♮ B ⟫
  map[]♮ = witness (curry⸢λ⸣ $ curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] map[]♭ mon[map[]♭]

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} where
  first♮ : ⟪ (A ↗ C) ↗ (A ∧♮ B) ↗ (C ∧♮ B) ⟫
  first♮ = witness (curry⸢λ⸣ $ curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] fun ppr
    where
      fun : ⟪ A ↗ C ⟫ → A ∧♭ B → C ∧♭ B
      fun f ⟨ x , y ⟩ = ⟨ f ⋅ x , y ⟩
      ppr : proper (_⊑♮_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr ⊑ᶠ ⟨ ⊑ˣ , ⊑ʸ ⟩ = ⟨ res[fx][↗]⸢⊑⸣ ⊑ᶠ ⊑ˣ , ⊑ʸ ⟩

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} {D : Poset ℓ₄} where
  [∘∘♮] : ⟪ (C ↗ D) ↗ (A ↗ B ↗ C) ↗ (A ↗ B ↗ D) ⟫
  [∘∘♮] = [∘♮] ∘♮ [∘♮]

  _∘∘♮_ : ⟪ C ↗ D ⟫ → ⟪ A ↗ B ↗ C ⟫ → ⟪ A ↗ B ↗ D ⟫
  g ∘∘♮ f = [∘∘♮] ⋅ g ⋅ f


module _ {ℓ} {A : Poset ℓ} where
  return[]♮ : ⟪ list♮ A ↗ ℘ A ⟫
  return[]♮ = witness (curry⸢λ♭⸣ id⸢ω⸣) $ mk[witness] fun ppr
    where
      fun : list♭ A → ⟪ A ⟫ → Set ℓ
      fun xs x = x ∈⊑ˡ♭ xs
      ppr : proper (_⊑_ ⇉ flip _⊑♮_ ⇉ [→]) fun
      ppr ⊑ₓₛ ⊑ₓ ∈ₓ = weaken[∈/L]ˡ♭ ⊑ₓ (weaken[∈/R]ˡ♭ ∈ₓ ⊑ₓₛ)
