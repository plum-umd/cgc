module Prelude.Data.Witness where

open import Prelude.Core
open import Prelude.Classes

infixr 11 _⇉ʷ_
infixr 30 ⊚[D]ʷ
infixl 50 _⋅ʷ_

record ⟪_⟫ʷ {ℓ ℓʳ} {A : Set ℓ} (_R_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  constructor mk[witness]
  field
    x : A
    x-proper : proper _R_ x

module §-⟪⟫ʷ {ℓ} {ℓʳ} {A : Set ℓ} {_R_ : relation ℓʳ A} (w : ⟪ _R_ ⟫ʷ) where
  open ⟪_⟫ʷ w

  witness : A
  witness = x
  proper[witness] : proper _R_ x
  proper[witness] = x-proper
open §-⟪⟫ʷ public

_⇉ʷ_ : ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ} {A : Set ℓ₁} (_R₁_ : relation ℓ₁ʳ A) {B : Set ℓ₂} (_R₂_ : relation ℓ₂ʳ B) → relation (ℓ₁ ⊔ᴸ ℓ₁ʳ ⊔ᴸ ℓ₂ʳ) (⟪ _R₁_ ⟫ʷ → B)
_R₁_ ⇉ʷ _R₂_ = (_R₁_ 𝑜𝑛 witness {_R_ = _R₁_}) ⇉ _R₂_

pureʷ :
  ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ} {A : Set ℓ₁} {_R₁_ : relation ℓ₁ʳ A} {B : Set ℓ₂} {_R₂_ : relation ℓ₂ʳ B}
  → ⟪ _R₁_ ⇉ _R₂_ ⟫ʷ → ⟪ _R₁_ ⇉ʷ  _R₂_ ⟫ʷ
pureʷ f = mk[witness] (witness f ∘ witness) (proper[witness] f)

_⋅ʷ_ :
  ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ} {A : Set ℓ₁} {_R₁_ : relation ℓ₁ʳ A} {B : Set ℓ₂} {_R₂_ : relation ℓ₂ʳ B}
  → ⟪ _R₁_ ⇉ʷ _R₂_ ⟫ʷ → ⟪ _R₁_ ⟫ʷ → ⟪ _R₂_ ⟫ʷ
f ⋅ʷ x = mk[witness] (witness f x) (proper[witness] f (proper[witness] x))

composeʷ[_,_,_] :
  ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ ℓ₃ ℓ₃ʳ} {A : Set ℓ₁} (_R₁_ : relation ℓ₁ʳ A) {B : Set ℓ₂} (_R₂_ : relation ℓ₂ʳ B) {C : Set ℓ₃} (_R₃_ : relation ℓ₃ʳ C)
  → ⟪ (_R₂_ ⇉ _R₃_) ⇉ʷ (_R₁_ ⇉ _R₂_) ⇉ʷ (_R₁_ ⇉ _R₃_) ⟫ʷ
composeʷ[_,_,_] {A = A} _R₁_ {B} _R₂_ {C} _R₃_ = mk[witness] f (λ {x} {y} → f-ppr {x} {y})
  where
    f : ⟪ _R₂_ ⇉ _R₃_ ⟫ʷ → ⟪ _R₁_ ⇉ _R₂_ ⟫ʷ → A → C
    f g f = witness g ∘ witness f
    f-ppr : proper ((_R₂_ ⇉ _R₃_) ⇉ʷ (_R₁_ ⇉ _R₂_) ⇉ʷ _R₁_ ⇉ _R₃_) f
    f-ppr g₁Rg₂ f₁Rf₂ = g₁Rg₂ ∘ f₁Rf₂

compose[D]ʷ[_,_,_] :
  ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ ℓ₃ ℓ₃ʳ} {A : Set ℓ₁} (_R₁_ : relation ℓ₁ʳ A) {B : Set ℓ₂} (_R₂_ : relation ℓ₂ʳ B) {C : Set ℓ₃} (_R₃_ : relation ℓ₃ʳ C)
  → ⟪ (_R₂_ ⇉ʷ _R₃_) ⇉ʷ (_R₁_ ⇉ʷ _R₂_) ⇉ʷ (_R₁_ ⇉ʷ _R₃_) ⟫ʷ
compose[D]ʷ[_,_,_] {A = A} _R₁_ {B} _R₂_ {C} _R₃_ = mk[witness] f (λ {x} {y} → f-ppr {x} {y})
  where
    f : ⟪ _R₂_ ⇉ʷ _R₃_ ⟫ʷ → ⟪ _R₁_ ⇉ʷ _R₂_ ⟫ʷ → ⟪ _R₁_ ⟫ʷ → C
    f g f x = witness g (mk[witness] (witness f x) ppr)
      where
        ppr : proper _R₂_ (witness f x)
        ppr = proper[witness] f (proper[witness] x)
    f-ppr : proper ((_R₂_ ⇉ʷ _R₃_) ⇉ʷ (_R₁_ ⇉ʷ _R₂_) ⇉ʷ _R₁_ ⇉ʷ _R₃_) f
    f-ppr g₁Rg₂ f₁Rf₂ = g₁Rg₂ ∘ f₁Rf₂

compose[DR₁]ʷ[_,_,_] : 
  ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ ℓ₃ ℓ₃ʳ} {A : Set ℓ₁} (_R₁_ : relation ℓ₁ʳ A) {B : Set ℓ₂} (_R₂_ : relation ℓ₂ʳ B) {C : Set ℓ₃} (_R₃_ : relation ℓ₃ʳ C)
    {{_ : Reflexive _R₁_}}
  → ⟪ (_R₂_ ⇉ʷ _R₃_) ⇉ʷ (_R₁_ ⇉ _R₂_) ⇉ʷ (_R₁_ ⇉ _R₃_) ⟫ʷ
compose[DR₁]ʷ[_,_,_] {A = A} _R₁_ {B} _R₂_ {C} _R₃_ {{REX}} = mk[witness] f (λ {x} {y} → f-ppr {x} {y})
  where
    f : ⟪ _R₂_ ⇉ʷ _R₃_ ⟫ʷ → ⟪ _R₁_ ⇉ _R₂_ ⟫ʷ → A → C
    f g f x = witness g (mk[witness] (witness f x) (fx-ppr (xRx {{REX}})))
      where
        fx-ppr : proper (_R₁_ ⇉ _R₂_) (λ x → witness f x)
        fx-ppr = ⟪_⟫ʷ.x-proper f
    f-ppr : proper ((_R₂_ ⇉ʷ _R₃_) ⇉ʷ (_R₁_ ⇉ _R₂_) ⇉ʷ _R₁_ ⇉ _R₃_) f
    f-ppr g₁Rg₂ f₁Rf₂ = g₁Rg₂ ∘ f₁Rf₂

pipe[DR₁]ʷ[_,_,_] :
  ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ ℓ₃ ℓ₃ʳ} {A : Set ℓ₁} (_R₁_ : relation ℓ₁ʳ A) {B : Set ℓ₂} (_R₂_ : relation ℓ₂ʳ B) {C : Set ℓ₃} (_R₃_ : relation ℓ₃ʳ C)
    {{_ : Reflexive _R₁_}}
  → ⟪ (_R₁_ ⇉ʷ _R₂_) ⇉ʷ (_R₂_ ⇉ _R₃_) ⇉ʷ (_R₁_ ⇉ _R₃_) ⟫ʷ
pipe[DR₁]ʷ[_,_,_] {A = A} _R₁_ {B} _R₂_ {C} _R₃_ {{REX}} = mk[witness] f (λ {x} {y} X {a} {b} C {d} {e} F → f-proper {x} {y} X {a} {b} C {d} {e} F)
  where
    f : ⟪ _R₁_ ⇉ʷ _R₂_ ⟫ʷ → ⟪ _R₂_ ⇉ _R₃_ ⟫ʷ → A → C
    f f g x = witness g (witness f (mk[witness] x (xRx {{REX}})))
    f-proper : proper ((_R₁_ ⇉ʷ _R₂_) ⇉ʷ (_R₂_ ⇉ _R₃_) ⇉ʷ _R₁_ ⇉ _R₃_) f
    f-proper f₁Rf₂ g₁Rg₂ = g₁Rg₂ ∘ f₁Rf₂

idʷ : ∀ {ℓ ℓʳ} {A : Set ℓ} {_R_ : relation ℓʳ A} → ⟪ _R_ ⇉ʷ _R_ ⟫ʷ
idʷ = mk[witness] witness id

syntax ⊚[D]ʷ {_R₁_ = _R₁_} {_R₂_ = _R₂_} {_R₃_ = _R₃_} G F = G ⊚[D]ʷ[ _R₁_ , _R₂_ , _R₃_ ] F
⊚[D]ʷ :
  ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ ℓ₃ ℓ₃ʳ} {A : Set ℓ₁} {_R₁_ : relation ℓ₁ʳ A} {B : Set ℓ₂} {_R₂_ : relation ℓ₂ʳ B} {C : Set ℓ₃} {_R₃_ : relation ℓ₃ʳ C}
  → ⟪ _R₂_ ⇉ʷ _R₃_ ⟫ʷ → ⟪ _R₁_ ⇉ʷ _R₂_ ⟫ʷ → ⟪ _R₁_ ⇉ʷ _R₃_ ⟫ʷ
⊚[D]ʷ {_R₁_ = _R₁_} {_R₂_ = _R₂_} {_R₃_ = _R₃_} g f = compose[D]ʷ[ _R₁_ , _R₂_ , _R₃_ ] ⋅ʷ g ⋅ʷ f

pipeʷ :
  ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ ℓ₃ ℓ₃ʳ} {A : Set ℓ₁} (_R₁_ : relation ℓ₁ʳ A) {B : Set ℓ₂} (_R₂_ : relation ℓ₂ʳ B) {C : Set ℓ₃} (_R₃_ : relation ℓ₃ʳ C)
  → ⟪ (_R₁_ ⇉ _R₂_) ⇉ʷ (_R₂_ ⇉ _R₃_) ⇉ʷ (_R₁_ ⇉ _R₃_) ⟫ʷ
pipeʷ {A = A} _R₁_ {B} _R₂_ {C} _R₃_ = mk[witness] f (λ {x} {y} → f-ppr {x} {y})
  where
    f : ⟪ _R₁_ ⇉ _R₂_ ⟫ʷ → ⟪ _R₂_ ⇉ _R₃_ ⟫ʷ → A → C
    f f g = witness g ∘ witness f
    f-ppr : proper ((_R₁_ ⇉ _R₂_) ⇉ʷ (_R₂_ ⇉ _R₃_) ⇉ʷ _R₁_ ⇉ _R₃_) f
    f-ppr f₁Rf₂ g₁Rg₂ = g₁Rg₂ ∘ f₁Rf₂

flipʷ[_,_] : ∀ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ} {A : Set ℓ₁} (_R₁_ : relation ℓ₁ʳ A) {B : Set ℓ₂} (_R₂_ : relation ℓ₂ʳ B) → ⟪ _R₁_ ⇉ʷ _R₂_ ⟫ʷ → ⟪ flip _R₁_ ⇉ʷ flip _R₂_ ⟫ʷ
flipʷ[_,_] {A = A} _R₁_ {B} _R₂_ f = mk[witness] F (λ {x} {y} → proper[F] {x} {y})
  where
    F : ⟪ flip _R₁_ ⟫ʷ → B
    F x = witness f (mk[witness] (witness x) (proper[witness] x))
    proper[F] : proper (flip _R₁_ ⇉ʷ flip _R₂_) F
    proper[F] xRy = proper[witness] f xRy
