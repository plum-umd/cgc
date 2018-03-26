module Prelude.Data.AddBot where

open import Prelude.Core
open import Prelude.Classes
open import Prelude.Orders

data add-⊥ {ℓ} (A : Set ℓ) : Set ℓ where
  ⊥ : add-⊥ A
  ⟨_⟩ : A → add-⊥ A

module _ {ℓ ℓʳ} {A : Set ℓ} {{_ : Order ℓʳ A}} where
  data _≤⸢add-⊥⸣_ : relation ℓʳ (add-⊥ A) where
    ⊥ : ∀ {x} → ⊥ ≤⸢add-⊥⸣ x
    ⟨_⟩ : ∀ {x y} → x ≤ y → ⟨ x ⟩ ≤⸢add-⊥⸣ ⟨ y ⟩
 
  xRx⸢≤⸢add-⊥⸣⸣ : reflexive _≤⸢add-⊥⸣_
  xRx⸢≤⸢add-⊥⸣⸣ {⊥} = ⊥
  xRx⸢≤⸢add-⊥⸣⸣ {⟨ x ⟩} = ⟨ xRx[≤][ A ] ⟩

  ⋈⸢≤⸢add-⊥⸣⸣ : antisymmetric _≤⸢add-⊥⸣_
  ⋈⸢≤⸢add-⊥⸣⸣ ⊥ ⊥ = ↯
  ⋈⸢≤⸢add-⊥⸣⸣ ⟨ ≤₁ ⟩ ⟨ ≥₁ ⟩ rewrite ⋈[≤][ A ] ≤₁ ≥₁ = ↯

  _⊚⸢≤⸢add-⊥⸣⸣_ : transitive _≤⸢add-⊥⸣_
  _ ⊚⸢≤⸢add-⊥⸣⸣ ⊥ = ⊥
  ⟨ ≤₂ ⟩ ⊚⸢≤⸢add-⊥⸣⸣ ⟨ ≤₁ ⟩ = ⟨ ≤₂ ⊚[≤][ A ] ≤₁ ⟩

  data _<⸢add-⊥⸣_ : relation ℓʳ (add-⊥ A) where
    ⊥ : ∀ {x} → ⊥ <⸢add-⊥⸣ ⟨ x ⟩
    ⟨_⟩ : ∀ {x y} → x < y → ⟨ x ⟩ <⸢add-⊥⸣ ⟨ y ⟩

  weaken[<]⸢add-⊥⸣ : ∀ {x y} → x <⸢add-⊥⸣ y → x ≤⸢add-⊥⸣ y
  weaken[<]⸢add-⊥⸣ ⊥ = ⊥
  weaken[<]⸢add-⊥⸣ {⟨ x ⟩} {⟨ y ⟩} ⟨ x<y ⟩ = ⟨ weaken[<][ A ] x<y ⟩

  strict[<]⸢add-⊥⸣ : ∀ {x y} → x <⸢add-⊥⸣ y → ¬ (y ≤⸢add-⊥⸣ x)
  strict[<]⸢add-⊥⸣ () ⊥
  strict[<]⸢add-⊥⸣ ⟨ x<y ⟩ ⟨ y≤x ⟩ = strict[<][ A ] x<y y≤x

  complete[<]⸢add-⊥⸣ : ∀ {x y} → x ≤⸢add-⊥⸣ y → ¬ (y ≤⸢add-⊥⸣ x) → x <⸢add-⊥⸣ y
  complete[<]⸢add-⊥⸣ {y = ⊥} ⊥ ¬y≤x = exfalso (¬y≤x ⊥)
  complete[<]⸢add-⊥⸣ {y = ⟨ _ ⟩} ⊥ ¬y≤x = ⊥
  complete[<]⸢add-⊥⸣ ⟨ x≤y ⟩ ¬y≤x = ⟨ complete[<][ A ] x≤y (λ y≤x → ¬y≤x ⟨ y≤x ⟩) ⟩

  _⋚⸢add-⊥⸣_ : add-⊥ A → add-⊥ A → ⪥!
  ⊥ ⋚⸢add-⊥⸣ ⊥ = [≡]
  ⊥ ⋚⸢add-⊥⸣ ⟨ _ ⟩ = [<]
  ⟨ _ ⟩ ⋚⸢add-⊥⸣ ⊥ = [>]
  ⟨ x ⟩ ⋚⸢add-⊥⸣ ⟨ y ⟩ = x ⋚ y

  _⋚ᴾ⸢add-⊥⸣_ : ∀ x y → x ⪥!ᴾ[ _<⸢add-⊥⸣_ ] y
  ⊥ ⋚ᴾ⸢add-⊥⸣ ⊥ = [≡] ↯
  ⊥ ⋚ᴾ⸢add-⊥⸣ ⟨ _ ⟩ = [<] ⊥
  ⟨ _ ⟩ ⋚ᴾ⸢add-⊥⸣ ⊥ = [>] ⊥
  ⟨ x ⟩ ⋚ᴾ⸢add-⊥⸣ ⟨ y ⟩ with x ⋚ᴾ y
  … | [<] <₁ = [<] ⟨ <₁ ⟩
  … | [≡] ≡₁ rewrite ≡₁ = [≡] ↯
  … | [>] >₁ = [>] ⟨ >₁ ⟩

  _⋚ᴸ⸢add-⊥⸣_ : ∀ x y → x ⪥!ᴸ[ _<⸢add-⊥⸣_ ] y ‖[ x ⋚⸢add-⊥⸣ y , x ⋚ᴾ⸢add-⊥⸣ y ]
  ⊥ ⋚ᴸ⸢add-⊥⸣ ⊥ = [≡]
  ⊥ ⋚ᴸ⸢add-⊥⸣ ⟨ _ ⟩ = [<]
  ⟨ _ ⟩ ⋚ᴸ⸢add-⊥⸣ ⊥ = [>]
  ⟨ x ⟩ ⋚ᴸ⸢add-⊥⸣ ⟨ y ⟩ with x ⋚ y | x ⋚ᴾ y | x ⋚ᴸ y
  … | [<] | [<] <₁ | [<] = [<]
  … | [≡] | [≡] ≡₁ | [≡] rewrite ≡₁ = [≡]
  … | [>] | [>] >₁ | [>] = [>]

  instance
    Reflexive[≤]⸢add-⊥⸣ : Reflexive _≤⸢add-⊥⸣_
    Reflexive[≤]⸢add-⊥⸣ = record { xRx = xRx⸢≤⸢add-⊥⸣⸣ }
    Antisymmetric[≤]⸢add-⊥⸣ : Antisymmetric _≤⸢add-⊥⸣_
    Antisymmetric[≤]⸢add-⊥⸣ = record { ⋈ = ⋈⸢≤⸢add-⊥⸣⸣ }
    Transitive[≤]⸢add-⊥⸣ : Transitive _≤⸢add-⊥⸣_
    Transitive[≤]⸢add-⊥⸣ = record { _⊚_ = _⊚⸢≤⸢add-⊥⸣⸣_ }
    Strict[<]⸢add-⊥⸣ : Strict _≤⸢add-⊥⸣_ _<⸢add-⊥⸣_
    Strict[<]⸢add-⊥⸣ = record
      { weaken[≺] = weaken[<]⸢add-⊥⸣
      ; strict[≺] = strict[<]⸢add-⊥⸣
      ; complete[≺] = complete[<]⸢add-⊥⸣
      }
    Irreflexive[<]⸢add-⊥⸣ : Irreflexive _<⸢add-⊥⸣_
    Irreflexive[<]⸢add-⊥⸣ = Irreflexive[<]/≤ _≤⸢add-⊥⸣_ _<⸢add-⊥⸣_
    Asymmetric[<]⸢add-⊥⸣ : Asymmetric _<⸢add-⊥⸣_
    Asymmetric[<]⸢add-⊥⸣ = Asymmetric[<]/≤ _≤⸢add-⊥⸣_ _<⸢add-⊥⸣_
    Transitive[<]⸢add-⊥⸣ : Transitive _<⸢add-⊥⸣_
    Transitive[<]⸢add-⊥⸣ = Transitive[<]/≤ _≤⸢add-⊥⸣_ _<⸢add-⊥⸣_
    Totally[<]⸢add-⊥⸣ : Totally _<⸢add-⊥⸣_
    Totally[<]⸢add-⊥⸣ = record
      { _⪥_ = _⋚⸢add-⊥⸣_
      ; _⪥ᴾ_ = _⋚ᴾ⸢add-⊥⸣_
      ; _⪥ᴸ_ = _⋚ᴸ⸢add-⊥⸣_
      }
    Order[<]⸢add-⊥⸣ : Order ℓʳ (add-⊥ A)
    Order[<]⸢add-⊥⸣ = mk[Order] _≤⸢add-⊥⸣_ _<⸢add-⊥⸣_

module _ {ℓ ℓʳ} {A : Set ℓ} {{_ : Precision ℓʳ A}} where
  data _⊑⸢add-⊥⸣_ : relation ℓʳ (add-⊥ A) where
    ⊥ : ∀ {x} → ⊥ ⊑⸢add-⊥⸣ x
    ⟨_⟩ : ∀ {x y} → x ⊑ y → ⟨ x ⟩ ⊑⸢add-⊥⸣ ⟨ y ⟩
 
  xRx⸢⊑⸢add-⊥⸣⸣ : reflexive _⊑⸢add-⊥⸣_
  xRx⸢⊑⸢add-⊥⸣⸣ {⊥} = ⊥
  xRx⸢⊑⸢add-⊥⸣⸣ {⟨ x ⟩} = ⟨ xRx[⊑][ A ] ⟩

  _⊚⸢⊑⸢add-⊥⸣⸣_ : transitive _⊑⸢add-⊥⸣_
  _ ⊚⸢⊑⸢add-⊥⸣⸣ ⊥ = ⊥
  ⟨ ⊑₂ ⟩ ⊚⸢⊑⸢add-⊥⸣⸣ ⟨ ⊑₁ ⟩ = ⟨ ⊑₂ ⊚[⊑][ A ] ⊑₁ ⟩

  instance
    Reflexive[⊑]⸢add-⊥⸣ : Reflexive _⊑⸢add-⊥⸣_
    Reflexive[⊑]⸢add-⊥⸣ = record { xRx = xRx⸢⊑⸢add-⊥⸣⸣ }
    Transitive[⊑]⸢add-⊥⸣ : Transitive _⊑⸢add-⊥⸣_
    Transitive[⊑]⸢add-⊥⸣ = record { _⊚_ = _⊚⸢⊑⸢add-⊥⸣⸣_ }
    Precision[add-⊥] : Precision ℓʳ (add-⊥ A)
    Precision[add-⊥] = mk[Precision] _⊑⸢add-⊥⸣_
