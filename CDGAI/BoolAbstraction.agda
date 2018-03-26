module CDGAI.BoolAbstraction where

open import Prelude
open import Poset

data 𝔹♯ : Set where
  True False None Any : 𝔹♯

data _⊑ᵇ♯_ : 𝔹♯ → 𝔹♯ → Set where
  True : True ⊑ᵇ♯ True
  False : False ⊑ᵇ♯ False
  Any : ∀ {b} → b ⊑ᵇ♯ Any
  None : ∀ {b} → None ⊑ᵇ♯ b

xRx⸢⊑ᵇ♯⸣ : ∀ {b} → b ⊑ᵇ♯ b
xRx⸢⊑ᵇ♯⸣ {True} = True
xRx⸢⊑ᵇ♯⸣ {False} = False
xRx⸢⊑ᵇ♯⸣ {None} = None
xRx⸢⊑ᵇ♯⸣ {Any} = Any

_⊚⸢⊑ᵇ♯⸣_ : ∀ {b₁ b₂ b₃} → b₂ ⊑ᵇ♯ b₃ → b₁ ⊑ᵇ♯ b₂ → b₁ ⊑ᵇ♯ b₃
True ⊚⸢⊑ᵇ♯⸣ True = True
False ⊚⸢⊑ᵇ♯⸣ False = False
Any ⊚⸢⊑ᵇ♯⸣ x = Any
x ⊚⸢⊑ᵇ♯⸣ None = None

instance
  Reflexive[⊑ᵇ♯] : Reflexive _⊑ᵇ♯_
  Reflexive[⊑ᵇ♯] = record { xRx = xRx⸢⊑ᵇ♯⸣ }
  Transitive[⊑ᵇ♯] : Transitive _⊑ᵇ♯_
  Transitive[⊑ᵇ♯] = record { _⊚_ = _⊚⸢⊑ᵇ♯⸣_ }
  Precision[⊑ᵇ♯] : Precision 0ᴸ 𝔹♯
  Precision[⊑ᵇ♯] = mk[Precision] _⊑ᵇ♯_

_⁇ᴾ[⊑ᵇ]_ : ∀ x y → x ‼ᴾ[ _⊑ᵇ♯_ ] y
None ⁇ᴾ[⊑ᵇ] _ = ✓ None
True ⁇ᴾ[⊑ᵇ] None = ✗ (λ ())
False ⁇ᴾ[⊑ᵇ] None = ✗ (λ ())
Any ⁇ᴾ[⊑ᵇ] None = ✗ (λ ())
_ ⁇ᴾ[⊑ᵇ] Any = ✓ Any
Any ⁇ᴾ[⊑ᵇ] True = ✗ (λ ())
Any ⁇ᴾ[⊑ᵇ] False = ✗ (λ ())
False ⁇ᴾ[⊑ᵇ] False = ✓ False
True ⁇ᴾ[⊑ᵇ] True = ✓ True
False ⁇ᴾ[⊑ᵇ] True = ✗ (λ ())
True ⁇ᴾ[⊑ᵇ] False = ✗ (λ ())

⁇ᴾ[⊑ᵇ]/is✓ : ∀ {x y} → x ⊑ᵇ♯ y → is✓[‼ᴾ] (x ⁇ᴾ[⊑ᵇ] y)
⁇ᴾ[⊑ᵇ]/is✓ {x} {y} ⊑₁ with x ⁇ᴾ[⊑ᵇ] y
… | ✓ ⊑₂ = ✓
… | ✗ ¬⊑ = exfalso (¬⊑ ⊑₁)

⁇ᴾ[⊑ᵇ]/is✗ : ∀ {x y} → ¬ (x ⊑ᵇ♯ y) → is✗[‼ᴾ] (x ⁇ᴾ[⊑ᵇ] y)
⁇ᴾ[⊑ᵇ]/is✗ {x} {y} ¬⊑₁ with x ⁇ᴾ[⊑ᵇ] y
… | ✓ ⊑₂ = exfalso (¬⊑₁ ⊑₂)
… | ✗ ¬⊑₂ = ✗

module _ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} where
  if∘♮ : ⟪ (A ↗ B) ↗ (A ↗ B) ↗ A ↗ ⇧ 𝔹 ↗ B ⟫
  if∘♮ = witness (curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ♭⸣ id⸢λ⸣) $ mk[witness] fun ppr
    where
      fun : ⟪ A ↗ B ⟫ → ⟪ A ↗ B ⟫ → ⟪ A ⟫ → 𝔹 → ⟪ B ⟫
      fun f g x b = if b then f ⋅ x else g ⋅ x
      ppr : proper (_⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_ ⇉ _⊑_ ⇉ _⊑♮_) fun
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ {True}  ↯ = res[fx][↗]⸢⊑⸣ ⊑ᶠ ⊑ˣ
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ {False} ↯ = res[fx][↗]⸢⊑⸣ ⊑ᵍ ⊑ˣ

  if∘♯ : ⟪ (A ↗ B) ↗ (A ↗ B) ↗ A ↗ ⇧ 𝔹♯ ↗ list♮ B ⟫
  if∘♯ = witness (curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ♭⸣ id⸢λ⸣) $ mk[witness] fun ppr
    where
      fun : ⟪ A ↗ B ⟫ → ⟪ A ↗ B ⟫ → ⟪ A ⟫ → 𝔹♯ → ⟪ list♮ B ⟫
      fun f g x True  = single♮ ⋅ (f ⋅ x)
      fun f g x False = single♮ ⋅ (g ⋅ x)
      fun f g x None  = []♮
      fun f g x Any   = single♮ ⋅ (f ⋅ x) ⧺♮ single♮ ⋅ (g ⋅ x)
      ppr : proper (_⊑♮_ ⇉ _⊑♮_ ⇉ _⊑♮_ ⇉ _⊑_ ⇉ _⊑♮_) fun
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ                True  = res[x][↗]⸢⊑⸣ {f = single♮} (res[fx][↗]⸢⊑⸣ ⊑ᶠ ⊑ˣ)
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ                False = res[x][↗]⸢⊑⸣ {f = single♮} (res[fx][↗]⸢⊑⸣ ⊑ᵍ ⊑ˣ)
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ {True}         Any   = ♮⟨ Zero (res[fx][↗]⸢⊑⸣ ⊑ᶠ ⊑ˣ) ∷ [] ⟩
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ {False}        Any   = ♮⟨ Succ (Zero (res[fx][↗]⸢⊑⸣ ⊑ᵍ ⊑ˣ)) ∷ [] ⟩
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ {None}         Any   = ♮⟨ [] ⟩
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ {Any}          Any   = ♮⟨ Zero (res[fx][↗]⸢⊑⸣ ⊑ᶠ ⊑ˣ) ∷ Succ (Zero (res[fx][↗]⸢⊑⸣ ⊑ᵍ ⊑ˣ)) ∷ [] ⟩
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ {None} {True}  None  = ♮⟨ [] ⟩
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ {None} {False} None  = ♮⟨ [] ⟩
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ {None} {None}  None  = ♮⟨ [] ⟩
      ppr ⊑ᶠ ⊑ᵍ ⊑ˣ {None} {Any}   None  = ♮⟨ [] ⟩

postulate
  ⇄𝔹⇄ : ⇧ 𝔹 ⇄ᶜ ⇧ 𝔹♯

module _ {A₁ A₂ B₁ B₂ : Poset 0ᴸ} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) where
  postulate
    α[if∘] :
      ∀ (tb₁ fb₁ : ⟪ A₁ ↗ B₁ ⟫) (tb₂ fb₂ : ⟪ A₂ ↗ B₂ ⟫)
      → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ (pure ⋅ tb₁) ⊑♮ pure ⋅ tb₂
      → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ (pure ⋅ fb₁) ⊑♮ pure ⋅ fb₂
      → α[ (⇄A⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄) ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ (pure ⋅ (uncurry♮ ⋅ (if∘♮ ⋅ tb₁ ⋅ fb₁))) ⊑♮ pure[]♮ ⋅ (uncurry♮ ⋅ (if∘♯ ⋅ tb₂ ⋅ fb₂))
