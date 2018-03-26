module Prelude.Data.Product where

open import Prelude.Core
open import Prelude.Classes
open import Prelude.Orders

module _ {ℓ₁ ℓʳ₁ ℓ₂ ℓʳ₂} {A : Set ℓ₁} {{_ : Order ℓʳ₁ A}} {B : Set ℓ₂} {{_ : Order ℓʳ₂ B}} where
  data _≤ˣ_ : relation (ℓʳ₁ ⊔ᴸ ℓʳ₂) (A ∧ B) where
    <[π₁] : ∀ {x₁ y₁ x₂ y₂} → x₁ < x₂ → ⟨ x₁ , y₁ ⟩ ≤ˣ ⟨ x₂ , y₂ ⟩
    ≤[π₂] : ∀ {x y₁ y₂} → y₁ ≤ y₂ → ⟨ x , y₁ ⟩ ≤ˣ ⟨ x , y₂ ⟩

  xRx⸢≤ˣ⸣ : reflexive _≤ˣ_
  xRx⸢≤ˣ⸣ {⟨ x , y ⟩} = ≤[π₂] xRx[≤][ B ]

  ⋈⸢≤ˣ⸣ : antisymmetric _≤ˣ_
  ⋈⸢≤ˣ⸣ (<[π₁] x₁<x₂) (<[π₁] x₂<x₁) = exfalso (¬◇[<][ A ] x₁<x₂ x₂<x₁)
  ⋈⸢≤ˣ⸣ (<[π₁] x₁<x₂) (≤[π₂] y₂≤y₁) = exfalso (¬xRx[<][ A ] x₁<x₂)
  ⋈⸢≤ˣ⸣ (≤[π₂] y₁≤y₂) (<[π₁] x₂<x₁) = exfalso (¬xRx[<][ A ] x₂<x₁)
  ⋈⸢≤ˣ⸣ (≤[π₂] y₁≤y₂) (≤[π₂] y₂≤y₁) rewrite ⋈[≤][ B ] y₁≤y₂ y₂≤y₁ = ↯

  _⊚⸢≤ˣ⸣_ : transitive _≤ˣ_
  <[π₁] x₂<x₃ ⊚⸢≤ˣ⸣ <[π₁] x₁<x₂ = <[π₁] (x₂<x₃ ⊚[<][ A ] x₁<x₂)
  <[π₁] x₂<x₃ ⊚⸢≤ˣ⸣ ≤[π₂] _ = <[π₁] x₂<x₃
  ≤[π₂] _ ⊚⸢≤ˣ⸣ <[π₁] x₁<x₂ = <[π₁] x₁<x₂
  ≤[π₂] y₂≤y₃ ⊚⸢≤ˣ⸣ ≤[π₂] y₁≤y₂ = ≤[π₂] (y₂≤y₃ ⊚[≤][ B ] y₁≤y₂)

  data _<ˣ_ : relation (ℓʳ₁ ⊔ᴸ ℓʳ₂) (A ∧ B) where
    <[π₁] : ∀ {x₁ y₁ x₂ y₂} → x₁ < x₂ → ⟨ x₁ , y₁ ⟩ <ˣ ⟨ x₂ , y₂ ⟩
    <[π₂] : ∀ {x y₁ y₂} → y₁ < y₂ → ⟨ x , y₁ ⟩ <ˣ ⟨ x , y₂ ⟩

  weaken[<]ˣ : ∀ {x y} → x <ˣ y → x ≤ˣ y
  weaken[<]ˣ (<[π₁] x₁<x₂) = <[π₁] x₁<x₂
  weaken[<]ˣ (<[π₂] y₁<y₂) = ≤[π₂] (weaken[<][ B ] y₁<y₂)

  strict[<]ˣ : ∀ {x y} → x <ˣ y → ¬ (y ≤ˣ x)
  strict[<]ˣ (<[π₁] x₁<x₂) (<[π₁] x₂<x₁) = ¬◇[<][ A ] x₁<x₂ x₂<x₁
  strict[<]ˣ (<[π₁] x₁<x₂) (≤[π₂] y₂≤y₁) = ¬xRx[<][ A ] x₁<x₂
  strict[<]ˣ (<[π₂] y₁<y₂) (<[π₁] x₂<x₁) = ¬xRx[<][ A ] x₂<x₁
  strict[<]ˣ (<[π₂] y₁<y₂) (≤[π₂] y₂≤y₁) = strict[<][ B ] y₁<y₂ y₂≤y₁

  complete[<]ˣ : ∀ {x y} → x ≤ˣ y → ¬ (y ≤ˣ x) → x <ˣ y
  complete[<]ˣ (<[π₁] x₁<x₂) ¬≤ = <[π₁] x₁<x₂
  complete[<]ˣ (≤[π₂] y₁≤y₂) ¬≤ = <[π₂] (complete[<][ B ] y₁≤y₂ (λ y₂≤y₁ → ¬≤ (≤[π₂] y₂≤y₁)))

  _⋚ˣ_ : A ∧ B → A ∧ B → ⪥!
  ⟨ x₁ , y₁ ⟩ ⋚ˣ ⟨ x₂ , y₂ ⟩ with x₁ ⋚ x₂
  … | [<] = [<]
  … | [>] = [>]
  … | [≡] with y₁ ⋚ y₂
  … | [<] = [<]
  … | [>] = [>]
  … | [≡] = [≡]

  _⋚ˣᴾ_ : ∀ x y → x ⪥!ᴾ[ _<ˣ_ ] y
  ⟨ x₁ , y₁ ⟩ ⋚ˣᴾ ⟨ x₂ , y₂ ⟩ with x₁ ⋚ᴾ x₂
  … | [<] x₁<x₂ = [<] (<[π₁] x₁<x₂)
  … | [>] x₁>x₂ = [>] (<[π₁] x₁>x₂)
  … | [≡] x₁≡x₂ rewrite x₁≡x₂ with y₁ ⋚ᴾ y₂
  … | [<] y₁<y₂ = [<] (<[π₂] y₁<y₂)
  … | [>] y₁>y₂ = [>] (<[π₂] y₁>y₂)
  … | [≡] y₁≡y₂ rewrite y₁≡y₂ = [≡] ↯

  _⋚ˣᴸ_ : ∀ x y → x ⪥!ᴸ[ _<ˣ_ ] y ‖[ x ⋚ˣ y , x ⋚ˣᴾ y ]
  ⟨ x₁ , y₁ ⟩ ⋚ˣᴸ ⟨ x₂ , y₂ ⟩ with x₁ ⋚ x₂ | x₁ ⋚ᴾ x₂ | x₁ ⋚ᴸ x₂
  … | [<] | [<] <ₓ | [<] = [<]
  … | [>] | [>] >ₓ | [>] = [>]
  … | [≡] | [≡] ≡ₓ | [≡] rewrite ≡ₓ with y₁ ⋚ y₂ | y₁ ⋚ᴾ y₂ | y₁ ⋚ᴸ y₂
  … | [<] | [<] <y | [<] = [<]
  … | [>] | [>] >y | [>] = [>]
  … | [≡] | [≡] ≡y | [≡] rewrite ≡y = [≡]

  instance
    Reflexive[≤]ˣ : Reflexive _≤ˣ_
    Reflexive[≤]ˣ = record { xRx = xRx⸢≤ˣ⸣ }
    Antisymmetric[≤]ˣ : Antisymmetric _≤ˣ_
    Antisymmetric[≤]ˣ = record { ⋈ = ⋈⸢≤ˣ⸣ }
    Transitive[≤]ˣ : Transitive _≤ˣ_
    Transitive[≤]ˣ = record { _⊚_ = _⊚⸢≤ˣ⸣_ }
    Strict[<]ˣ : Strict _≤ˣ_ _<ˣ_
    Strict[<]ˣ = record { weaken[≺] = weaken[<]ˣ ; strict[≺] = strict[<]ˣ ; complete[≺] = complete[<]ˣ }
    Irreflexive[<]ˣ : Irreflexive _<ˣ_
    Irreflexive[<]ˣ = Irreflexive[<]/≤ _≤ˣ_ _<ˣ_
    Asymmetric[<]ˣ : Asymmetric _<ˣ_
    Asymmetric[<]ˣ = Asymmetric[<]/≤ _≤ˣ_ _<ˣ_
    Transitive[<]ˣ : Transitive _<ˣ_
    Transitive[<]ˣ = Transitive[<]/≤ _≤ˣ_ _<ˣ_
    Totally[<]ˣ : Totally _<ˣ_
    Totally[<]ˣ = record
      { _⪥_ = _⋚ˣ_
      ; _⪥ᴾ_ = _⋚ˣᴾ_
      ; _⪥ᴸ_ = _⋚ˣᴸ_
      }
    Order[∧] : Order (ℓʳ₁ ⊔ᴸ ℓʳ₂) (A ∧ B)
    Order[∧] = mk[Order] _≤ˣ_ _<ˣ_

module _ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ} {A : Set ℓ₁} {{_ : Precision ℓ₁ʳ A}} {B : Set ℓ₂} {{_ : Precision ℓ₂ʳ B}} where
  data _⊑ˣ_ : A ∧ B → A ∧ B → Set (ℓ₁ ⊔ᴸ ℓ₂ ⊔ᴸ ℓ₁ʳ ⊔ᴸ ℓ₂ʳ) where
    ⟨_,_⟩ : ∀ {x₁ y₁ x₂ y₂} → x₁ ⊑ x₂ → y₁ ⊑ y₂ → ⟨ x₁ , y₁ ⟩ ⊑ˣ ⟨ x₂ , y₂ ⟩

  xRx⸢⊑ˣ⸣ : reflexive _⊑ˣ_
  xRx⸢⊑ˣ⸣ {⟨ _ , _ ⟩} = ⟨ xRx[⊑][ A ] , xRx[⊑][ B ] ⟩

  _⊚⸢⊑ˣ⸣_ : transitive _⊑ˣ_
  ⟨ ⊑₁₁ , ⊑₂₁ ⟩ ⊚⸢⊑ˣ⸣ ⟨ ⊑₁₂ , ⊑₂₂ ⟩ = ⟨ ⊑₁₁ ⊚[⊑][ A ] ⊑₁₂ , ⊑₂₁ ⊚[⊑][ B ] ⊑₂₂ ⟩

  instance
    Reflexive[⊑ˣ] : Reflexive _⊑ˣ_
    Reflexive[⊑ˣ] = record { xRx = xRx⸢⊑ˣ⸣ }
    Transitive[⊑ˣ] : Transitive _⊑ˣ_
    Transitive[⊑ˣ] = record { _⊚_ = _⊚⸢⊑ˣ⸣_ }
    Precision[∧] : Precision (ℓ₁ ⊔ᴸ ℓ₂ ⊔ᴸ ℓ₁ʳ ⊔ᴸ ℓ₂ʳ) (A ∧ B)
    Precision[∧] = mk[Precision] _⊑ˣ_
