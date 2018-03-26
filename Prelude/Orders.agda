module Prelude.Orders where

open import Prelude.Core
open import Prelude.Classes

record Order {ℓ} ℓʳ (A : Set ℓ) : Set (ℓ ⊔ᴸ ↑ᴸ ℓʳ) where
  infix 14 _≤_
  infix 14 _≥_
  infix 14 _<_
  infix 14 _>_
  infixr 22 _⩔_
  infixr 24 _⩓_
  field
    _≤_ : relation ℓʳ A
    {{Reflexive[≤]}} : Reflexive _≤_
    {{Antisymmetric[≤]}} : Antisymmetric _≤_
    {{Transitive[≤]}} : Transitive _≤_
    _<_ : relation ℓʳ A
    {{Irreflexive[<]}} : Irreflexive _<_
    {{Asymmetric[<]}} : Asymmetric _<_
    {{Transitive[<]}} : Transitive _<_
    {{Strict[≤/<]}} : Strict _≤_ _<_
    {{Totally[<]}} : Totally _<_
    -- z ≤ (x ⩔ y) ↔ z ≤ x ∨ z ≤ y
    -- (x ⩔ y) ≤ z ↔ x ≤ z ∧ y ≤ z
    -- x ≤ y ↔ (x ⩔ y) ≡ y
    _⩔_ : A → A → A
    left-bound[⩔] : ∀ {x y} → x ≤ x ⩔ y
    right-bound[⩔] : ∀ {x y} → y ≤ x ⩔ y
    tight[⩔] : ∀ {x y z} → x ≤ z → y ≤ z → x ⩔ y ≤ z
    _⩓_ : A → A → A
    left-bound[⩓] : ∀ {x y} → x ⩓ y ≤ x
    right-bound[⩓] : ∀ {x y} → x ⩓ y ≤ y
    tight[⩓] : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ x ⩓ y
  _≥_ : relation ℓʳ A
  _≥_ = flip _≤_
  _>_ : relation ℓʳ A
  _>_ = flip _<_
  open Reflexive Reflexive[≤] public renaming
    ( xRx to xRx[≤]
    ; xRx[≡] to xRx[≡][≤]
    )
  open Antisymmetric Antisymmetric[≤] public renaming ( ⋈ to ⋈[≤] )
  open Transitive Transitive[≤] public renaming ( _⊚_ to _⊚[≤]_ )
  open Irreflexive Irreflexive[<] public renaming
    ( ¬xRx to ¬xRx[<]
    ; ¬xRx[≡] to ¬xRx[≡][<]
    )
  open Asymmetric Asymmetric[<] public renaming ( ¬◇ to ¬◇[<] )
  open Transitive Transitive[<] public renaming ( _⊚_ to _⊚[<]_ )
  open Strict Strict[≤/<] public using () renaming
    ( weaken[≺]  to weaken[<]
    ; strict[≺] to strict[<]
    ; complete[≺] to complete[<]
    ; strict[≺]/≡ to strict[<]/≡
    )
  open Totally Totally[<] public renaming
    ( _⪥_       to _⋚_
    ; _⪥ᴾ_      to _⋚ᴾ_
    ; _⪥ᴸ_      to _⋚ᴸ_
    ; ⪥[≡]      to ⋚[≡]
    ; ⪥[<]      to ⋚[<]
    ; ⪥[>]      to ⋚[>]
    ; flip[⪥]/≡ to flip[⋚]/≡
    )
  complete[⩔] : ∀ {x y z} → x ≤ z → y ≤ z → (∀ {z⁺} → x ≤ z⁺ → y ≤ z⁺ → z ≤ z⁺) → x ⩔ y ≡ z
  complete[⩔] x≤z y≤z F = ⋈[≤] (tight[⩔] x≤z y≤z) (F left-bound[⩔] right-bound[⩔])
  left-order[⩔] : ∀ {x y} → x ≤ y → x ⩔ y ≡ y
  left-order[⩔] x≤y = ⋈[≤] (tight[⩔] x≤y xRx[≤]) right-bound[⩔]
  right-order[⩔] : ∀ {x y} → y ≤ x → x ⩔ y ≡ x
  right-order[⩔] y≤x = ⋈[≤] (tight[⩔] xRx[≤] y≤x) left-bound[⩔]
  tight[⩔]/< : ∀ {x y z} → x < z → y < z → x ⩔ y < z
  tight[⩔]/< {x} {y} {z} x<z y<z = complete[<] (tight[⩔] (weaken[<] x<z) (weaken[<] y<z)) (P (x ⋚ᴾ y))
    where
      P : x ⪥!ᴾ[ _<_ ] y → z ≤ x ⩔ y → void
      P ([<] x<y) z≤x⩔y rewrite left-order[⩔] (weaken[<] x<y) = strict[<] y<z z≤x⩔y
      P ([≡] x≡y) z≤x⩔y rewrite left-order[⩔] (xRx[≡][≤] x≡y) = strict[<] y<z z≤x⩔y
      P ([>] x>y) z≤x⩔y rewrite right-order[⩔] (weaken[<] x>y) = strict[<] x<z z≤x⩔y
  associative[⩔] : ∀ {x y z} → (x ⩔ y) ⩔ z ≡ x ⩔ y ⩔ z
  associative[⩔] =
    ⋈[≤] (tight[⩔] (tight[⩔] left-bound[⩔] (right-bound[⩔] ⊚[≤] left-bound[⩔]))
                   (right-bound[⩔] ⊚[≤] right-bound[⩔]))
         (tight[⩔] (left-bound[⩔] ⊚[≤] left-bound[⩔])
                   (tight[⩔] (left-bound[⩔] ⊚[≤] right-bound[⩔]) right-bound[⩔]))
  commutative[⩔] : ∀ {x y} → x ⩔ y ≡ y ⩔ x
  commutative[⩔] =
    ⋈[≤] (tight[⩔] right-bound[⩔] left-bound[⩔])
         (tight[⩔] right-bound[⩔] left-bound[⩔])
  idempotent[⩔] : ∀ {x} → x ⩔ x ≡ x
  idempotent[⩔] = ⋈[≤] (tight[⩔] xRx[≤] xRx[≤]) left-bound[⩔]
  dec-bound[⩔] : ∀ {x y z} → z ≤ x ⩔ y → z ≤ x ∨ z ≤ y
  dec-bound[⩔] {x} {y} z≤x⩔y with x ⋚ᴾ y
  … | [<] x<y rewrite left-order[⩔] (weaken[<] x<y) = Inr z≤x⩔y
  … | [≡] x≡y rewrite x≡y | idempotent[⩔] {x = y} = Inr z≤x⩔y
  … | [>] x>y rewrite commutative[⩔] {x = x} {y} | left-order[⩔] (weaken[<] x>y) = Inl z≤x⩔y
  complete[⩓] : ∀ {x y z} → z ≤ x → z ≤ y → (∀ {z⁻} → z⁻ ≤ x → z⁻ ≤ y → z⁻ ≤ z) → x ⩓ y ≡ z
  complete[⩓] x≤z y≤z F = ⋈[≤] (F left-bound[⩓] right-bound[⩓]) (tight[⩓] x≤z y≤z)
  left-order[⩓] : ∀ {x y} → x ≤ y → x ⩓ y ≡ x
  left-order[⩓] x≤y = ⋈[≤] left-bound[⩓] (tight[⩓] xRx[≤] x≤y)
  right-order[⩓] : ∀ {x y} → y ≤ x → x ⩓ y ≡ y
  right-order[⩓] y≤x = ⋈[≤] right-bound[⩓] (tight[⩓] y≤x xRx[≤])
  tight[⩓]/< : ∀ {x y z} → z < x → z < y → z < x ⩓ y
  tight[⩓]/< {x} {y} {z} z<x z<y = complete[<] (tight[⩓] (weaken[<] z<x) (weaken[<] z<y)) (P (x ⋚ᴾ y))
    where
      P : x ⪥!ᴾ[ _<_ ] y → x ⩓ y ≤ z → void
      P ([<] x<y) x⩓y≤z rewrite left-order[⩓] (weaken[<] x<y) = strict[<] z<x x⩓y≤z
      P ([≡] x≡y) x⩓y≤z rewrite left-order[⩓] (xRx[≡][≤] x≡y) = strict[<] z<x x⩓y≤z
      P ([>] x>y) x⩓y≤z rewrite right-order[⩓] (weaken[<] x>y) = strict[<] z<y x⩓y≤z
  associative[⩓] : ∀ {x y z} → (x ⩓ y) ⩓ z ≡ x ⩓ y ⩓ z
  associative[⩓] =
    ⋈[≤] (tight[⩓] (left-bound[⩓] ⊚[≤] left-bound[⩓])
                (tight[⩓] (right-bound[⩓] ⊚[≤] left-bound[⩓])
                          right-bound[⩓]))
         (tight[⩓] (tight[⩓] left-bound[⩓]
                             (left-bound[⩓] ⊚[≤] right-bound[⩓]))
                   (right-bound[⩓] ⊚[≤] right-bound[⩓]))
  commutative[⩓] : ∀ {x y} → x ⩓ y ≡ y ⩓ x
  commutative[⩓] =
    ⋈[≤] (tight[⩓] right-bound[⩓] left-bound[⩓])
         (tight[⩓] right-bound[⩓] left-bound[⩓])
  idempotent[⩓] : ∀ {x} → x ⩓ x ≡ x
  idempotent[⩓] = ⋈[≤] left-bound[⩓] (tight[⩓] xRx[≤] xRx[≤])
  dec-bound[⩓] : ∀ {x y z} → x ⩓ y ≤ z → x ≤ z ∨ y ≤ z
  dec-bound[⩓] {x} {y} x⩓y≤z with x ⋚ᴾ y
  … | [<] x<y rewrite left-order[⩓] (weaken[<] x<y) = Inl x⩓y≤z
  … | [≡] x≡y rewrite x≡y | idempotent[⩓] {x = y} = Inr x⩓y≤z
  … | [>] x>y rewrite commutative[⩓] {x = x} {y} | left-order[⩓] (weaken[<] x>y) = Inr x⩓y≤z
open Order {{…}} public

module _ {ℓ ℓʳ} (A : Set ℓ) {{ℭ : Order ℓʳ A}} where
  ≤[_] = Order._≤_ ℭ
  <[_] = Order._<_ ℭ
  ⩔[_] = Order._⩔_ ℭ
  ⩓[_] = Order._⩓_ ℭ
  xRx[≤][_] = Order.xRx[≤] ℭ
  ⋈[≤][_] = Order.⋈[≤] ℭ
  ¬xRx[<][_] = Order.¬xRx[<] ℭ
  ¬◇[<][_] = Order.¬◇[<] ℭ
  weaken[<][_] = Order.weaken[<] ℭ
  strict[<][_] = Order.strict[<] ℭ
  strict[<]/≡[_] = Order.strict[<]/≡ ℭ
  complete[<][_] = Order.complete[<] ℭ
  left-bound[⩔][_] = Order.left-bound[⩔] ℭ
  right-bound[⩔][_] = Order.right-bound[⩔] ℭ
  tight[⩔][_] = Order.tight[⩔] ℭ
  complete[⩔][_] = Order.complete[⩔] ℭ
  left-order[⩔][_] = Order.left-order[⩔] ℭ
  right-order[⩔][_] = Order.right-order[⩔] ℭ
  tight[⩔]/<[_] = Order.tight[⩔]/< ℭ
  left-bound[⩓][_] = Order.left-bound[⩓] ℭ
  right-bound[⩓][_] = Order.right-bound[⩓] ℭ
  tight[⩓][_] = Order.tight[⩓] ℭ
  complete[⩓][_] = Order.complete[⩓] ℭ
  left-order[⩓][_] = Order.left-order[⩓] ℭ
  right-order[⩓][_] = Order.right-order[⩓] ℭ
  tight[⩓]/<[_] = Order.tight[⩓]/< ℭ
  ⋚[≡][_] = Order.⋚[≡] ℭ
  ⋚[<][_] = Order.⋚[<] ℭ
  ⋚[>][_] = Order.⋚[>] ℭ
  
  infixr 30 ⊚[≤][]
  infixr 30 ⊚[<][]

  syntax ⋚[] A x y = x ⋚[ A ] y
  ⋚[] = Order._⋚_ ℭ
  syntax ⋚ᴾ[] A x y = x ⋚ᴾ[ A ] y
  ⋚ᴾ[] = Order._⋚ᴾ_ ℭ
  syntax ⋚ᴸ[] A x y = x ⋚ᴸ[ A ] y
  ⋚ᴸ[] = Order._⋚ᴸ_ ℭ

  syntax ⊚[≤][] A x y = x ⊚[≤][ A ] y
  ⊚[≤][] = Order._⊚[≤]_ ℭ
  syntax ⊚[<][] A x y = x ⊚[<][ A ] y
  ⊚[<][] = Order._⊚[<]_ ℭ

record Discrete[≤] {ℓ ℓʳ} (A : Set ℓ) {{_ : Order ℓʳ A}} : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    discrete[≤] : ∀ {x y : A} (p₁ : x ≤ y) (p₂ : x ≤ y) → p₁ ≡ p₂
open Discrete[≤] {{…}} public

module _ {ℓ ℓʳ} (A : Set ℓ) {{_ : Order ℓʳ A}} {{ℭ : Discrete[≤] A}} where
  discrete[≤][_] = Discrete[≤].discrete[≤] ℭ

record Top[≤] {ℓ ℓʳ} (A : Set ℓ) {{_ : Order ℓʳ A}} : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    ⊤[≤] : A
    bound[⊤]/≤ : ∀ {x} → x ≤ ⊤[≤]
  complete[⊤]/≤ : ∀ {x} → (∀ {y} → y ≤ x) → x ≡ ⊤[≤]
  complete[⊤]/≤ F = ⋈[≤] bound[⊤]/≤ F
  left-unit[⊤]/≤ : ∀ {x} → ⊤[≤] ⩓ x ≡ x
  left-unit[⊤]/≤ = ⋈[≤] (right-bound[⩓][ A ]) (tight[⩓][ A ]  bound[⊤]/≤  xRx[≤][ A ])
  left-unit[⊤]/≤[_] : ∀ x → ⊤[≤] ⩓ x ≡ x
  left-unit[⊤]/≤[ x ] = left-unit[⊤]/≤
  right-unit[⊤]/≤ : ∀ {x} → x ⩓ ⊤[≤] ≡ x
  right-unit[⊤]/≤ = ⋈[≤] left-bound[⩓][ A ] (tight[⩓][ A ]  xRx[≤][ A ]  bound[⊤]/≤)
  right-unit[⊤]/≤[_] : ∀ x → x ⩓ ⊤[≤] ≡ x
  right-unit[⊤]/≤[ x ] = right-unit[⊤]/≤
  left-zero[⊤]/≤ : ∀ {x} → ⊤[≤] ⩔ x ≡ ⊤[≤]
  left-zero[⊤]/≤ = ⋈[≤] (tight[⩔][ A ] xRx[≤][ A ] bound[⊤]/≤) left-bound[⩔][ A ]
  right-zero[⊤]/≤ : ∀ {x} → x ⩔ ⊤[≤] ≡ ⊤[≤]
  right-zero[⊤]/≤ = ⋈[≤] (tight[⩔][ A ] bound[⊤]/≤ xRx[≤][ A ]) right-bound[⩔][ A ]
open Top[≤] {{…}} public

module _ {ℓ ℓʳ} {A : Set ℓ}
  (_≤_ : relation ℓʳ A) {{_ : Reflexive _≤_}} {{_ : Antisymmetric _≤_}} {{_ : Transitive _≤_}}
  (_<_ : relation ℓʳ A) {{_ : Strict _≤_ _<_}}
  where
  ¬xRx[<]/≤ : irreflexive _<_
  ¬xRx[<]/≤ {x} x<x = strict[≺] x<x (xRx {_≼_ =  _≤_})
  ¬◇[<]/≤ : asymmetric _<_
  ¬◇[<]/≤ x<y y<x = strict[≺] {_≼_ = _≤_} x<y (weaken[≺] y<x)
  ⊚[<]/≤[_,_] : transitive _<_
  ⊚[<]/≤[_,_] y<z x<y = complete[≺] {_≼_ = _≤_} (weaken[≺] y<z ⊚ weaken[≺] x<y) (λ x≤z → strict[≺] y<z (weaken[≺] x<y ⊚ x≤z))
  Irreflexive[<]/≤ : Irreflexive _<_
  Irreflexive[<]/≤ = record { ¬xRx = ¬xRx[<]/≤ }
  Asymmetric[<]/≤ : Asymmetric _<_
  Asymmetric[<]/≤ = record { ¬◇ = ¬◇[<]/≤ }
  Transitive[<]/≤ : Transitive _<_
  Transitive[<]/≤ = record { _⊚_ = ⊚[<]/≤[_,_] }

module _ {ℓ ℓʳ} {A : Set ℓ} (_<_ : relation ℓʳ A) {{_ : Irreflexive _<_}} {{_ : Asymmetric _<_}} {{_ : Totally _<_}} where
  syntax ⩔/<[] _<_ x y = x ⩔/<[ _<_ ] y
  ⩔/<[] : A → A → A
  ⩔/<[] x y with x ⪥[ _<_ ] y
  … | [<] = y
  … | [≡] = x
  … | [>] = x
  syntax ⩓/<[] _<_ x y = x ⩓/<[ _<_ ] y
  ⩓/<[] : A → A → A
  ⩓/<[] x y with x ⪥[ _<_ ] y
  … | [<] = x
  … | [≡] = x
  … | [>] = y

module _ {ℓ ℓʳ} {A : Set ℓ}
  (_≤_ : relation ℓʳ A) {{_ : Reflexive _≤_}} {{_ : Antisymmetric _≤_}} {{_ : Transitive _≤_}}
  (_<_ : relation ℓʳ A) {{_ : Irreflexive _<_}} {{_ : Asymmetric _<_}} {{_ : Totally _<_}} {{_ : Strict _≤_ _<_}}
  where
  left-bound[⩔]/⪥ : ∀ {x y} → x ≤ (x ⩔/<[ _<_ ] y)
  left-bound[⩔]/⪥ {x} {y} with x ⪥[ _<_ ] y | x ⪥ᴾ[ _<_ ] y | id (x ⪥ᴸ[ _<_ ] y)
  … | [<] | [<] x<y | [<] = weaken[≺] x<y
  … | [≡] | [≡] x≡y | [≡] = xRx
  … | [>] | [>] x>y | [>] = xRx
  right-bound[⩔]/⪥ : ∀ {x y} → y ≤ (x ⩔/<[ _<_ ] y)
  right-bound[⩔]/⪥ {x} {y} with x ⪥[ _<_ ] y | x ⪥ᴾ[ _<_ ] y | id (x ⪥ᴸ[ _<_ ] y)
  … | [<] | [<] x<y | [<] = xRx
  … | [≡] | [≡] x≡y | [≡] rewrite x≡y = xRx
  … | [>] | [>] x>y | [>] = weaken[≺] x>y
  tight[⩔]/⪥ : ∀ {x y z} → x ≤ z → y ≤ z → (x ⩔/<[ _<_ ] y) ≤ z
  tight[⩔]/⪥ {x} {y} {z} x≤z y≤z with id (x ⪥[ _<_ ] y)
  … | [<] = y≤z
  … | [≡] = x≤z
  … | [>] = x≤z
  left-bound[⩓]/⪥ : ∀ {x y} → (x ⩓/<[ _<_ ] y) ≤ x
  left-bound[⩓]/⪥ {x} {y} with x ⪥[ _<_ ] y | x ⪥ᴾ[ _<_ ] y | id (x ⪥ᴸ[ _<_ ] y)
  … | [<] | [<] x<y | [<] = xRx
  … | [≡] | [≡] x≡y | [≡] = xRx
  … | [>] | [>] x>y | [>] = weaken[≺] x>y
  right-bound[⩓]/⪥ : ∀ {x y} → (x ⩓/<[ _<_ ] y) ≤ y
  right-bound[⩓]/⪥ {x} {y} with x ⪥[ _<_ ] y | x ⪥ᴾ[ _<_ ] y | id (x ⪥ᴸ[ _<_ ] y)
  … | [<] | [<] x<y | [<] = weaken[≺] x<y
  … | [≡] | [≡] x≡y | [≡] rewrite x≡y = xRx
  … | [>] | [>] x>y | [>] = xRx
  tight[⩓]/⪥ : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ (x ⩓/<[ _<_ ] y)
  tight[⩓]/⪥ {x} {y} {z} z≤x z≤y with id (x ⪥[ _<_ ] y)
  … | [<] = z≤x
  … | [≡] = z≤x
  … | [>] = z≤y

module _ {ℓ ℓʳ} {A : Set ℓ}
  (_≼_ : relation ℓʳ A) {{_ : Reflexive _≼_}} {{_ : Antisymmetric _≼_}} {{_ : Transitive _≼_}}
  (_≺_ : relation ℓʳ A) {{_ : Irreflexive _≺_}} {{_ : Asymmetric _≺_}} {{_ : Transitive _≺_}} {{_ : Strict _≼_ _≺_}} {{_ : Totally _≺_}}
  where
  mk[Order] : Order ℓʳ A
  mk[Order] = record
    { _≤_ = _≼_
    ; _<_ = _≺_
    ; _⩔_ = ⩔/<[] _≺_
    ; left-bound[⩔] = left-bound[⩔]/⪥ _≼_ _≺_
    ; right-bound[⩔] = right-bound[⩔]/⪥ _≼_ _≺_
    ; tight[⩔] = tight[⩔]/⪥ _≼_ _≺_
    ; _⩓_ = ⩓/<[] _≺_
    ; left-bound[⩓] = left-bound[⩓]/⪥ _≼_ _≺_
    ; right-bound[⩓] = right-bound[⩓]/⪥ _≼_ _≺_
    ; tight[⩓] = tight[⩓]/⪥ _≼_ _≺_
    }

---------------
-- Precision --
---------------

record Precision {ℓ} ℓʳ (A : Set ℓ) : Set (ℓ ⊔ᴸ ↑ᴸ ℓʳ) where
  infix 14 _⊑_
  infix 14 _⊒_
  field
    _⊑_ : relation ℓʳ A
    {{Reflexive[⊑]}} : Reflexive _⊑_
    {{Transitive[⊑]}} : Transitive _⊑_
    _≈_ : relation ℓʳ A
    xRx[≈/⊑] : ∀ {x y} → x ≈ y → x ⊑ y
    _⊚[≈]_ : ∀ {x y z} → y ≈ z → x ≈ y → x ≈ z
    ⋈[⊑] : ∀ {x y} → x ⊑ y → y ⊑ x → x ≈ y
  _⊒_ : relation ℓʳ A
  _⊒_ = flip _⊑_
  open Reflexive Reflexive[⊑] public renaming
    ( xRx to xRx[⊑]
    ; xRx[≡] to xRx[≡/⊑]
    )
  open Transitive Transitive[⊑] public renaming ( _⊚_ to _⊚[⊑]_ )
  xRx[≈] : ∀ {x} → x ≈ x
  xRx[≈] = ⋈[⊑] xRx[⊑] xRx[⊑]
open Precision {{…}} public

module _ {ℓ ℓʳ} (A : Set ℓ) {{ℭ : Precision ℓʳ A}} where
  ⊑[_] = Precision._⊑_ ℭ
  xRx[⊑][_] = Precision.xRx[⊑] ℭ
  ⋈[⊑][_] = Precision.⋈[⊑] ℭ

  syntax ⊚[⊑][] A x y = x ⊚[⊑][ A ] y
  ⊚[⊑][] : transitive ⊑[_]
  ⊚[⊑][] = Precision._⊚[⊑]_ ℭ
  syntax ⊑[[]] A x y = x ⊑[[ A ]] y
  ⊑[[]] : relation ℓʳ A
  ⊑[[]] = Precision._⊑_ ℭ

module _ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) {{_ : Reflexive _≼_}} {{_ : Transitive _≼_}} where
  _≈/⊑_ : relation ℓʳ A
  x ≈/⊑ y = x ≼ y ∧ y ≼ x

  xRx[≈/⊑]/⊑ : ∀ {x y} → x ≈/⊑ y → x ≼ y
  xRx[≈/⊑]/⊑ = π₁

  _⊚[≈]/⊑_ : ∀ {x y z} → y ≈/⊑ z → x ≈/⊑ y → x ≈/⊑ z
  ⟨ y⊑z , z⊑y ⟩ ⊚[≈]/⊑ ⟨ x⊑y , y⊑x ⟩ = ⟨ y⊑z ⊚ x⊑y , y⊑x ⊚ z⊑y ⟩

  ⋈[⊑]/⊑ : ∀ {x y} → x ≼ y → y ≼ x → x ≈/⊑ y
  ⋈[⊑]/⊑ = ⟨_,_⟩

  mk[Precision] : Precision ℓʳ A
  mk[Precision] = record
    { _⊑_ = _≼_
    ; _≈_ = _≈/⊑_
    ; xRx[≈/⊑] = xRx[≈/⊑]/⊑
    ; _⊚[≈]_ = _⊚[≈]/⊑_
    ; ⋈[⊑] = ⋈[⊑]/⊑
    }

record Top[⊑] {ℓ ℓʳ} (A : Set ℓ) {{_ : Precision ℓʳ A}} : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    ⊤[⊑] : A
    bound[⊤]/⊑ : ∀ {x} → x ⊑ ⊤[⊑]
  complete[⊤]/⊑ : ∀ {x} → (∀ {y} → y ⊑ x) → x ≈ ⊤[⊑]
  complete[⊤]/⊑ F = ⋈[⊑][ A ] bound[⊤]/⊑ F
open Top[⊑] {{…}} public


record DecLt {ℓ} (A : Set ℓ) {{_ : Order ℓ A}} : Set ℓ where
  field
    {{DecRel[<]}} : DecRel <[ A ]
  open DecRel DecRel[<] public using () renaming
    ( _⁇_ to _⁇[<]_
    ; _⁇ᴾ_ to _⁇ᴾ[<]_
    ; _⁇ᴮ_ to _⁇ᴮ[<]_
    )
open DecLt {{…}} public

record DecLte {ℓ} (A : Set ℓ) {{_ : Order ℓ A}} : Set ℓ where
  field
    {{DecRel[≤]}} : DecRel ≤[ A ]
  open DecRel DecRel[≤] public using () renaming
    ( _⁇_ to _⁇[≤]_
    ; _⁇ᴾ_ to _⁇ᴾ[≤]_
    ; _⁇ᴮ_ to _⁇ᴮ[≤]_
    )
open DecLte {{…}} public
