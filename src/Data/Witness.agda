module Data.Witness where

open import Prelude

record ⟪_⟫⸢W⸣ {𝓁 𝓁ʳ} {A : Set 𝓁} (_R_ : relation 𝓁ʳ A) : Set (𝓁 ⊔ˡ 𝓁ʳ) where
  constructor mk[witness]
  field
    x : A
    x-proper : proper _R_ x

module §-⟪⟫⸢W⸣ {𝓁} {𝓁ʳ} {A : Set 𝓁} {_R_ : relation 𝓁ʳ A} (w : ⟪ _R_ ⟫⸢W⸣) where
  open ⟪_⟫⸢W⸣ w

  witness-x : A
  witness-x = x
  witness-proper : proper _R_ x
  witness-proper = x-proper
open §-⟪⟫⸢W⸣ public

infixr 4 _⇉⸢W⸣_
_⇉⸢W⸣_ : ∀ {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ} {A : Set 𝓁₁} (_R₁_ : relation 𝓁₁ʳ A) {B : Set 𝓁₂} (_R₂_ : relation 𝓁₂ʳ B) → relation (𝓁₁ ⊔ˡ 𝓁₁ʳ ⊔ˡ 𝓁₂ʳ) (⟪ _R₁_ ⟫⸢W⸣ → B)
_R₁_ ⇉⸢W⸣ _R₂_ = (_R₁_ 𝑜𝑛 witness-x {_R_ = _R₁_}) ⇉ _R₂_

infixr 4 _⇒⸢W⸣_
_⇒⸢W⸣_ : ∀ {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ} {A : Set 𝓁₁} (_R₁_ : relation 𝓁₁ʳ A) {B : Set 𝓁₂} (_R₂_ : relation 𝓁₂ʳ B) → Set (𝓁₁ ⊔ˡ 𝓁₁ʳ ⊔ˡ 𝓁₂ ⊔ˡ 𝓁₂ʳ)
_R₁_ ⇒⸢W⸣ _R₂_ = ⟪ _R₁_ ⇉⸢W⸣ _R₂_ ⟫⸢W⸣

pure⸢W⸣ :
  ∀ {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ} {A : Set 𝓁₁} {_R₁_ : relation 𝓁₁ʳ A} {B : Set 𝓁₂} {_R₂_ : relation 𝓁₂ʳ B}
  → ⟪ _R₁_ ⇉ _R₂_ ⟫⸢W⸣ → _R₁_ ⇒⸢W⸣ _R₂_
pure⸢W⸣ f = mk[witness] (witness-x f ∘ witness-x) (witness-proper f)

infixl 20 _⋅⸢W⸣_
_⋅⸢W⸣_ :
  ∀ {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ} {A : Set 𝓁₁} {_R₁_ : relation 𝓁₁ʳ A} {B : Set 𝓁₂} {_R₂_ : relation 𝓁₂ʳ B}
  → (_R₁_ ⇒⸢W⸣ _R₂_) → ⟪ _R₁_ ⟫⸢W⸣ → ⟪ _R₂_ ⟫⸢W⸣
f ⋅⸢W⸣ x = mk[witness] (witness-x f x) (witness-proper f (witness-proper x))

compose⸢W⸣[_,_,_] :
  ∀ {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ 𝓁₃ 𝓁₃ʳ} {A : Set 𝓁₁} (_R₁_ : relation 𝓁₁ʳ A) {B : Set 𝓁₂} (_R₂_ : relation 𝓁₂ʳ B) {C : Set 𝓁₃} (_R₃_ : relation 𝓁₃ʳ C)
  → ⟪ (_R₂_ ⇉ _R₃_) ⇉⸢W⸣ (_R₁_ ⇉ _R₂_) ⇉⸢W⸣ (_R₁_ ⇉ _R₃_) ⟫⸢W⸣
compose⸢W⸣[_,_,_] {A = A} _R₁_ {B} _R₂_ {C} _R₃_ = mk[witness] f (λ {x} {y} → f-ppr {x} {y})
  where
    f : ⟪ _R₂_ ⇉ _R₃_ ⟫⸢W⸣ → ⟪ _R₁_ ⇉ _R₂_ ⟫⸢W⸣ → A → C
    f g f = witness-x g ∘ witness-x f
    f-ppr : proper ((_R₂_ ⇉ _R₃_) ⇉⸢W⸣ (_R₁_ ⇉ _R₂_) ⇉⸢W⸣ _R₁_ ⇉ _R₃_) f
    f-ppr g₁Rg₂ f₁Rf₂ = g₁Rg₂ ∘ f₁Rf₂

compose[D]⸢W⸣[_,_,_] :
  ∀ {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ 𝓁₃ 𝓁₃ʳ} {A : Set 𝓁₁} (_R₁_ : relation 𝓁₁ʳ A) {B : Set 𝓁₂} (_R₂_ : relation 𝓁₂ʳ B) {C : Set 𝓁₃} (_R₃_ : relation 𝓁₃ʳ C)
  → ⟪ (_R₂_ ⇉⸢W⸣ _R₃_) ⇉⸢W⸣ (_R₁_ ⇉⸢W⸣ _R₂_) ⇉⸢W⸣ (_R₁_ ⇉⸢W⸣ _R₃_) ⟫⸢W⸣
compose[D]⸢W⸣[_,_,_] {A = A} _R₁_ {B} _R₂_ {C} _R₃_ = mk[witness] f (λ {x} {y} → f-ppr {x} {y})
  where
    f : ⟪ _R₂_ ⇉⸢W⸣ _R₃_ ⟫⸢W⸣ → ⟪ _R₁_ ⇉⸢W⸣ _R₂_ ⟫⸢W⸣ → ⟪ _R₁_ ⟫⸢W⸣ → C
    f g f x = witness-x g (mk[witness] (witness-x f x) ppr)
      where
        ppr : proper _R₂_ (witness-x f x)
        ppr = witness-proper f (witness-proper x)
    f-ppr : proper ((_R₂_ ⇉⸢W⸣ _R₃_) ⇉⸢W⸣ (_R₁_ ⇉⸢W⸣ _R₂_) ⇉⸢W⸣ _R₁_ ⇉⸢W⸣ _R₃_) f
    f-ppr g₁Rg₂ f₁Rf₂ = g₁Rg₂ ∘ f₁Rf₂

compose[DR₁]⸢W⸣[_,_,_] : 
  ∀ {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ 𝓁₃ 𝓁₃ʳ} {A : Set 𝓁₁} (_R₁_ : relation 𝓁₁ʳ A) {B : Set 𝓁₂} (_R₂_ : relation 𝓁₂ʳ B) {C : Set 𝓁₃} (_R₃_ : relation 𝓁₃ʳ C)
    {{REX : Reflexive _R₁_}}
  → ⟪ (_R₂_ ⇉⸢W⸣ _R₃_) ⇉⸢W⸣ (_R₁_ ⇉ _R₂_) ⇉⸢W⸣ (_R₁_ ⇉ _R₃_) ⟫⸢W⸣
compose[DR₁]⸢W⸣[_,_,_] {A = A} _R₁_ {B} _R₂_ {C} _R₃_ = mk[witness] f (λ {x} {y} → f-ppr {x} {y})
  where
    f : ⟪ _R₂_ ⇉⸢W⸣ _R₃_ ⟫⸢W⸣ → ⟪ _R₁_ ⇉ _R₂_ ⟫⸢W⸣ → A → C
    f g f x = witness-x g (mk[witness] (witness-x f x) (fx-ppr xRx))
      where
        fx-ppr : proper (_R₁_ ⇉ _R₂_) (λ x → witness-x f x)
        fx-ppr = ⟪_⟫⸢W⸣.x-proper f
    f-ppr : proper ((_R₂_ ⇉⸢W⸣ _R₃_) ⇉⸢W⸣ (_R₁_ ⇉ _R₂_) ⇉⸢W⸣ _R₁_ ⇉ _R₃_) f
    f-ppr g₁Rg₂ f₁Rf₂ = g₁Rg₂ ∘ f₁Rf₂

id⸢W⸣ : ∀ {𝓁 𝓁ʳ} {A : Set 𝓁} {_R_ : relation 𝓁ʳ A} → ⟪ _R_ ⇉⸢W⸣ _R_ ⟫⸢W⸣
id⸢W⸣ = mk[witness] witness-x id

syntax ⌾[D]⸢W⸣ {_R₁_ = _R₁_} {_R₂_ = _R₂_} {_R₃_ = _R₃_} G F = G ⌾[D]⸢W⸣[ _R₁_ , _R₂_ , _R₃_ ] F
⌾[D]⸢W⸣ :
  ∀ {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ 𝓁₃ 𝓁₃ʳ} {A : Set 𝓁₁} {_R₁_ : relation 𝓁₁ʳ A} {B : Set 𝓁₂} {_R₂_ : relation 𝓁₂ʳ B} {C : Set 𝓁₃} {_R₃_ : relation 𝓁₃ʳ C}
  → ⟪ _R₂_ ⇉⸢W⸣ _R₃_ ⟫⸢W⸣ → ⟪ _R₁_ ⇉⸢W⸣ _R₂_ ⟫⸢W⸣ → ⟪ _R₁_ ⇉⸢W⸣ _R₃_ ⟫⸢W⸣
⌾[D]⸢W⸣ {_R₁_ = _R₁_} {_R₂_ = _R₂_} {_R₃_ = _R₃_} g f = compose[D]⸢W⸣[ _R₁_ , _R₂_ , _R₃_ ] ⋅⸢W⸣ g ⋅⸢W⸣ f

pipe⸢W⸣ :
  ∀ {𝓁₁ 𝓁₁ʳ 𝓁₂ 𝓁₂ʳ 𝓁₃ 𝓁₃ʳ} {A : Set 𝓁₁} (_R₁_ : relation 𝓁₁ʳ A) {B : Set 𝓁₂} (_R₂_ : relation 𝓁₂ʳ B) {C : Set 𝓁₃} (_R₃_ : relation 𝓁₃ʳ C)
  → ⟪ (_R₁_ ⇉ _R₂_) ⇉⸢W⸣ (_R₂_ ⇉ _R₃_) ⇉⸢W⸣ (_R₁_ ⇉ _R₃_) ⟫⸢W⸣
pipe⸢W⸣ {A = A} _R₁_ {B} _R₂_ {C} _R₃_ = mk[witness] f (λ {x} {y} → f-ppr {x} {y})
  where
    f : ⟪ _R₁_ ⇉ _R₂_ ⟫⸢W⸣ → ⟪ _R₂_ ⇉ _R₃_ ⟫⸢W⸣ → A → C
    f f g = witness-x g ∘ witness-x f
    f-ppr : proper ((_R₁_ ⇉ _R₂_) ⇉⸢W⸣ (_R₂_ ⇉ _R₃_) ⇉⸢W⸣ _R₁_ ⇉ _R₃_) f
    f-ppr f₁Rf₂ g₁Rg₂ = g₁Rg₂ ∘ f₁Rf₂
