module Prelude.Classes where

open import Prelude.Core

----------------
-- Arithmetic --
----------------

record Additive {ℓ} (A : Set ℓ) : Set ℓ where
  infixr 22 _+_
  field
    zero : A
    _+_ : A → A → A
    left-unit[+] : ∀ x → zero + x ≡ x
    right-unit[+] : ∀ x → x + zero ≡ x
    associative[+] : ∀ x y z → (x + y) + z ≡ x + y + z
    commutative[+] : ∀ x y → x + y ≡ y + x
open Additive {{…}} public

record Subtractive {ℓ} (A : Set ℓ) {{_ : Additive A}} : Set ℓ where
  infix 23 _-_
  infixr 60 ⁻_
  field
    _-_ : A → A → A
    correct[-] : ∀ x y → x + (y - x) ≡ y
  ⁻_ : A → A
  ⁻ x = zero - x
open Subtractive {{…}} public

record Subtractive/OK {ℓ} (A : Set ℓ) : Set (↑ᴸ ℓ) where
  field
    ok[_-_] : A → A → Set ℓ
open Subtractive/OK {{…}} public

record Subtractive/P {ℓ} (A : Set ℓ) {{_ : Additive A}} {{_ : Subtractive/OK A}} : Set ℓ where
  infix 23 _-_‖_
  field
    _-_‖_ : ∀ x y → ok[ x - y ] → A
    correct[-‖] : ∀ x y (ok[x-y] : ok[ x - y ]) → y + (x - y ‖ ok[x-y]) ≡ x
open Subtractive/P {{…}} public

record Multiplicative {ℓ} (A : Set ℓ) {{_ : Additive A}} : Set ℓ where
  infixr 24 _×_
  field
    one : A
    _×_ : A → A → A
    left-unit[×] : ∀ x → one × x ≡ x
    right-unit[×] : ∀ x → x × one ≡ x
    left-zero[×] : ∀ x → zero × x ≡ zero
    right-zero[×] : ∀ x → x × zero ≡ zero
    associative[×] : ∀ x y z → (x × y) × z ≡ x × y × z
    commutative[×] : ∀ x y → x × y ≡ y × x
    distributive[×] : ∀ x y z → (x + y) × z ≡ x × z + y × z
open Multiplicative {{…}} public

record DivMod {ℓ} (A : Set ℓ) {{_ : Additive A}} {{_ : Multiplicative A}} : Set ℓ where
  infix  25 _/%_
  field
    _/%_ : A → A → A ∧ A
    correct[/%] : ∀ x y → let ⟨ q , r ⟩ = x /% y in y × q + r ≡ x
open DivMod {{…}} public 

record DivMod/OK {ℓ} (A : Set ℓ) : Set (↑ᴸ ℓ) where
  field
    ok[_/%_] : A → A → Set ℓ
open DivMod/OK {{…}} public

record DivMod/P {ℓ} (A : Set ℓ) {{_ : Additive A}} {{_ : Multiplicative A}} {{_ : DivMod/OK A}} : Set ℓ where
  infix  25 _/%_‖_
  field
    _/%_‖_ : ∀ x y → ok[ x /% y ] → A ∧ A
    correct[/%‖] : ∀ x y (ok[x/%y] : ok[ x /% y ]) → let ⟨ q , r ⟩ = x /% y ‖ ok[x/%y] in y × q + r ≡ x
open DivMod/P {{…}} public

module _ {ℓ} {A : Set ℓ} {{_ : Additive A}} {{_ : Multiplicative A}} {{_ : DivMod/OK A}} {{_ : DivMod/P A}} where
  infix 25 _/_‖_
  _/_‖_ : ∀ (x y : A) → ok[ x /% y ] → A
  x / y ‖ ok = π₁ (x /% y ‖ ok)
  infix 23 _%_‖_
  _%_‖_ : ∀ (x y : A) → ok[ x /% y ] → A
  x % y ‖ ok = π₂ (x /% y ‖ ok)

-------------
-- Monoid  --
-------------

record Monoid {ℓ} (A : Set ℓ) : Set ℓ where
  infixr 22 _⧺_
  field
    null : A
    _⧺_ : A → A → A
    left-unit[⧺] : ∀ x → null ⧺ x ≡ x
    right-unit[⧺] : ∀ x → x ⧺ null ≡ x
    associative[⧺] : ∀ x y z → (x ⧺ y) ⧺ z ≡ x ⧺ (y ⧺ z)
open Monoid {{…}} public

-------------
-- Functor --
-------------

record Functor {ℓ} (F : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  field
    map : ∀ {A B : Set ℓ} → (A → B) → F A → F B
    unit[map] : ∀ {A : Set ℓ} (t : F A) → (map id) t ≡ id t
    homo[map] : ∀ {A B C : Set ℓ} (g : B → C) (f : A → B) (t : F A) → map (g ∘ f) t ≡ (map g ∘ map f) t
open Functor {{…}} public

-----------
-- Monad --
-----------

record Monad {ℓ} (M : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  infixr 1 bind
  syntax bind X (λ x → e) = x ← X ‣ e
  field
    return : ∀ {A : Set ℓ} → A → M A
    bind : ∀ {A B : Set ℓ} → M A → (A → M B) → M B
    left-unit[bind] : ∀ {A B : Set ℓ} (x : A) (f : A → M B) → bind (return x) f ≡ f x
    right-unit[bind] : ∀ {A : Set ℓ} (xM : M A) → bind xM return ≡ xM
    associative[bind] : ∀ {A B C : Set ℓ} (xM : M A) (f : A → M B) (g : B → M C) → bind (bind xM f) g ≡ bind xM (λ x → bind (f x) g)
  _≫=_ : ∀ {A B : Set ℓ} → M A → (A → M B) → M B
  _≫=_ = bind
  _* : ∀ {A B : Set ℓ} → (A → M B) → M A → M B
  (f *) X = X ≫= f
  _^⋅_ : ∀ {A B : Set ℓ} → (A → B) → M A → M B
  f ^⋅ X =
    do x ← X
     ‣ return (f x)
  -- I'd like either syntax support for this (syntax with multiple
  -- binders) or support for patterns in syntax
  bind₂ : ∀ {A B C : Set ℓ} → M (A ∧ B) → (A → B → M C) → M C
  bind₂ XY f =
    do xy ← XY
     ‣ let ⟨ x , y ⟩ = xy in
       f x y
open Monad {{…}} public

record MonadPlus {ℓ} (M : Set ℓ → Set ℓ) {{_ : Monad M}} : Set (↑ᴸ ℓ) where
  infixr 22 _⊞_
  field
    mzero : ∀ {A : Set ℓ} → M A
    _⊞_ : ∀ {A : Set ℓ} → M A → M A → M A
    left-unit[⊞] : ∀ {A : Set ℓ} (xM : M A) → mzero ⊞ xM ≡ xM
    right-unit[⊞] : ∀ {A : Set ℓ} (xM : M A) → xM ⊞ mzero ≡ xM
    associative[⊞] : ∀ {A : Set ℓ} (xM₁ xM₂ xM₃ : M A) → (xM₁ ⊞ xM₂) ⊞ xM₃ ≡ xM₁ ⊞ xM₂ ⊞ xM₃
    commutative[⊞] : ∀ {A : Set ℓ} (xM₁ xM₂ : M A) → xM₁ ⊞ xM₂ ≡ xM₂ ⊞ xM₁
    left-zero[⊞] : ∀ {A B : Set ℓ} (f : A → M B) → bind mzero f ≡ mzero
    right-zero[⊞] : ∀ {A : Set ℓ} (xM : M A) → bind xM (λ _ → mzero 𝑎𝑡 M A) ≡ mzero
    distributive[bind] : ∀ {A B : Set ℓ} (xM₁ xM₂ : M A) (f : A → M B) → bind (xM₁ ⊞ xM₂) f ≡ bind xM₁ f ⊞ bind xM₂ f

---------------
-- Relations --
---------------

reflexive : ∀ {ℓ ℓʳ} {A : Set ℓ} → relation ℓʳ A → Set (ℓ ⊔ᴸ ℓʳ)
reflexive _≼_ = ∀ {x} → x ≼ x

record Reflexive {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    xRx : reflexive _≼_
  xRx[≡] : ∀ {x y} → x ≡ y → x ≼ y
  xRx[≡] ↯ = xRx
open Reflexive {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) {{ℭ : Reflexive _≼_}} where
  xRx[_] = Reflexive.xRx ℭ
  xRx[≡][_] = Reflexive.xRx[≡] ℭ

irreflexive : ∀ {ℓ ℓʳ} {A : Set ℓ} → relation ℓʳ A → Set (ℓ ⊔ᴸ ℓʳ)
irreflexive _≼_ = ∀ {x} → ¬ (x ≼ x)

record Irreflexive {ℓ ℓʳ} {A : Set ℓ} (_≺_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    ¬xRx : irreflexive _≺_
  ¬xRx[≡] : ∀ {x y} → x ≡ y → ¬ (x ≺ y)
  ¬xRx[≡] ↯ = ¬xRx
open Irreflexive {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) {{ℭ : Irreflexive _≼_}} where
  ¬xRx[_] = Irreflexive.¬xRx ℭ
  ¬xRx[≡][_] = Irreflexive.¬xRx[≡] ℭ
  

transitive : ∀ {ℓ ℓʳ} {A : Set ℓ} → relation ℓʳ A → Set (ℓ ⊔ᴸ ℓʳ)
transitive _≼_ = ∀ {x y z} → y ≼ z → x ≼ y → x ≼ z

symmetric : ∀ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) → Set (ℓ ⊔ᴸ ℓʳ)
symmetric _≼_ = ∀ {x y} → x ≼ y → y ≼ x

record Symmetric {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    ◇ : symmetric _≼_
open Symmetric {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) {{ℭ : Symmetric _≼_}} where
  ◇[_] = Symmetric.◇ ℭ

asymmetric : ∀ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) → Set (ℓ ⊔ᴸ ℓʳ)
asymmetric _≼_ = ∀ {x y} → x ≼ y → ¬ (y ≼ x)

record Asymmetric {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    ¬◇ : asymmetric _≼_
open Asymmetric {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) {{ℭ : Asymmetric _≼_}} where
  ¬◇[_] = Asymmetric.¬◇ ℭ

antisymmetric : ∀ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) → Set (ℓ ⊔ᴸ ℓʳ)
antisymmetric _≼_ = ∀ {x y} → x ≼ y → y ≼ x → x ≡ y

record Antisymmetric {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    ⋈ : antisymmetric _≼_
open Antisymmetric {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) {{ℭ : Antisymmetric _≼_}} where
  ⋈[_] = Antisymmetric.⋈ ℭ

record Transitive {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  infixr 30 _⊚_
  field
    _⊚_ : transitive _≼_
open Transitive {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) {{ℭ : Transitive _≼_}} where
  syntax ⊚[] _≼_ x y = x ⊚[ _≼_ ] y
  ⊚[] = Transitive._⊚_ ℭ

reflexiveᴳ : ∀ {ℓ ℓᵉ ℓʳ} {A : Set ℓ} → relation ℓᵉ A → relation ℓʳ A → Set (ℓ ⊔ᴸ ℓᵉ ⊔ᴸ ℓʳ)
reflexiveᴳ _~_ _≼_ = ∀ {x y} → x ~ y → x ≼ y

record Reflexiveᴳ {ℓ ℓᵉ ℓʳ} {A : Set ℓ} (_~_ : relation ℓᵉ A) (_≼_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓᵉ ⊔ᴸ ℓʳ) where
  field
    xRxᴳ : reflexiveᴳ _~_  _≼_
open Reflexiveᴳ {{…}} public
module _ {ℓ ℓᵉ ℓʳ} {A : Set ℓ} (_~_ : relation ℓᵉ A) (_≼_ : relation ℓʳ A) {{ℭ : Reflexiveᴳ _~_ _≼_}} where
  xRxᴳ[_,_] = Reflexiveᴳ.xRxᴳ ℭ

antisymmetricᴳ : ∀ {ℓ ℓᵉ ℓʳ} {A : Set ℓ} (_~_ : relation ℓᵉ A) (_≼_ : relation ℓʳ A) → Set (ℓ ⊔ᴸ ℓᵉ ⊔ᴸ ℓʳ)
antisymmetricᴳ _~_ _≼_ = ∀ {x y} → x ≼ y → y ≼ x → x ~ y

record Antisymmetricᴳ {ℓ ℓʳ} {A : Set ℓ} (_~_ : relation ℓʳ A) (_≼_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    ⋈ᴳ : antisymmetricᴳ _~_ _≼_
open Antisymmetricᴳ {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (_~_ : relation ℓʳ A) (_≼_ : relation ℓʳ A) {{ℭ : Antisymmetricᴳ _~_ _≼_}} where
  ⋈ᴳ[_,_] = Antisymmetricᴳ.⋈ᴳ ℭ

record Strict {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) {{_ : Reflexive _≼_}} {{_ : Transitive _≼_}} (_≺_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    weaken[≺] : ∀ {x y} → x ≺ y → x ≼ y
    strict[≺] : ∀ {x y} → x ≺ y → ¬ (y ≼ x)
    complete[≺] : ∀ {x y} → x ≼ y → ¬ (y ≼ x) → x ≺ y
  strict[≺]/≡ : ∀ {x y} → x ≺ y → ¬ (x ≡ y)
  strict[≺]/≡ x≺y x≡y = strict[≺] x≺y (xRx[≡] (◇⸢≡⸣ x≡y))
  extend[≺]/L : ∀ {x y z} → x ≼ y → y ≺ z → x ≺ z
  extend[≺]/L ≼₁ ≺₂ = complete[≺] (weaken[≺] ≺₂ ⊚ ≼₁) (λ z≼x → strict[≺] ≺₂ (≼₁ ⊚ z≼x))
  extend[≺]/R : ∀ {x y z} → x ≺ y → y ≼ z → x ≺ z
  extend[≺]/R ≺₁ ≼₂ = complete[≺] (≼₂ ⊚ weaken[≺] ≺₁) (λ z≼x → strict[≺] ≺₁ (z≼x ⊚ ≼₂))
open Strict {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) {{_ : Reflexive _≼_}} {{_ : Transitive _≼_}} (_≺_ : relation ℓʳ A) {{ℭ : Strict _≼_ _≺_}} where
  weaken[≺][_,_] = Strict.weaken[≺] ℭ
  strict[≺][_,_] = Strict.strict[≺] ℭ
  complete[≺][_,_] = Strict.complete[≺] ℭ
  strict[≺]/≡[_,_] = Strict.strict[≺]/≡ ℭ

record Category {ℓ ℓʳ} {A : Set ℓ} (_≼_ : A → A → Set ℓʳ) {{_ : Reflexive _≼_}} {{_ : Transitive _≼_}} : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    left-unit : ∀ {x y} (f : x ≼ y) → xRx ⊚ f ≡ f
    right-unit : ∀ {x y} (f : x ≼ y) → f ⊚ xRx ≡ f
    associative : ∀ {w x y z} (h : y ≼ z) (g : x ≼ y) (f : w ≼ x) → (h ⊚ g) ⊚ f ≡ h ⊚ g ⊚ f
open Category {{…}} public

------------------------------
-- Decidable Total Relation --
------------------------------

data ⪥! : Set where [<] [≡] [>] : ⪥!

flip[⪥] : ⪥! → ⪥!
flip[⪥] [<] = [>]
flip[⪥] [≡] = [≡]
flip[⪥] [>] = [<]

syntax ⪥!ᴾ[] _≺_ x y = x ⪥!ᴾ[ _≺_ ] y
data ⪥!ᴾ[] {ℓ ℓʳ} {A : Set ℓ} (_≺_ : relation ℓʳ A) (x y : A) : Set (ℓ ⊔ᴸ ℓʳ) where
  [<] : x ≺ y → x ⪥!ᴾ[ _≺_ ] y
  [≡] : x ≡ y → x ⪥!ᴾ[ _≺_ ] y
  [>] : y ≺ x → x ⪥!ᴾ[ _≺_ ] y

flip[⪥ᴾ] : ∀ {ℓ ℓʳ} {A : Set ℓ} {_≺_ : relation ℓʳ A} {x y : A} → x ⪥!ᴾ[ _≺_ ] y → y ⪥!ᴾ[ _≺_ ] x
flip[⪥ᴾ] ([<] x<y) = [>] x<y
flip[⪥ᴾ] ([≡] x≡y) = [≡] (◇⸢≡⸣ x≡y)
flip[⪥ᴾ] ([>] x>y) = [<] x>y

syntax ⪥!ᴸ[] _≺_ x y r rᴾ = x ⪥!ᴸ[ _≺_ ] y ‖[ r , rᴾ ]
data ⪥!ᴸ[] {ℓ ℓʳ} {A : Set ℓ} (_≺_ : relation ℓʳ A) (x y : A) : ⪥! → x ⪥!ᴾ[ _≺_ ] y → Set (ℓ ⊔ᴸ ℓʳ) where
  [<] : ∀ {E : x ≺ y} → x ⪥!ᴸ[ _≺_ ] y ‖[ [<] , [<] E ]
  [≡] : ∀ {E : x ≡ y} → x ⪥!ᴸ[ _≺_ ] y ‖[ [≡] , [≡] E ]
  [>] : ∀ {E : y ≺ x} → x ⪥!ᴸ[ _≺_ ] y ‖[ [>] , [>] E ]

record Totally {ℓ ℓʳ} {A : Set ℓ} (_≺_ : relation ℓʳ A) {{_ : Irreflexive _≺_}} {{_ : Asymmetric _≺_}} : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    _⪥_ : A → A → ⪥!
    _⪥ᴾ_ : ∀ (x y : A) → x ⪥!ᴾ[ _≺_ ] y
    _⪥ᴸ_ : ∀ (x y : A) → x ⪥!ᴸ[ _≺_ ] y ‖[ x ⪥ y , x ⪥ᴾ y ]
  ⪥[≡] : ∀ x y → x ≡ y → x ⪥ y ≡ [≡]
  ⪥[≡] x .x ↯ with x ⪥ x | x ⪥ᴾ x | x ⪥ᴸ x
  … | [<] | [<] x<x | [<] = exfalso (¬xRx x<x)
  … | [≡] | [≡] _ | [≡] = ↯
  … | [>] | [>] x>x | [>] = exfalso (¬xRx x>x)
  ⪥[<] : ∀ x y → x ≺ y → x ⪥ y ≡ [<]
  ⪥[<] x y x<y with x ⪥ y | x ⪥ᴾ y | x ⪥ᴸ y
  … | [<] | [<] _ | [<] = ↯
  … | [≡] | [≡] x≡y | [≡] rewrite x≡y = exfalso (¬xRx x<y)
  … | [>] | [>] x>y | [>] = exfalso (¬◇ x>y x<y)
  ⪥[>] : ∀ x y → y ≺ x → x ⪥ y ≡ [>]
  ⪥[>] x y x>y with x ⪥ y | x ⪥ᴾ y | x ⪥ᴸ y
  … | [<] | [<] x<y | [<] = exfalso (¬◇ x<y x>y)
  … | [≡] | [≡] x≡y | [≡] rewrite x≡y = exfalso (¬xRx x>y)
  … | [>] | [>] _ | [>] = ↯
  flip[⪥]/≡ : ∀ x y → x ⪥ y ≡ flip[⪥] (y ⪥ x)
  flip[⪥]/≡ x y with x ⪥ y | x ⪥ᴾ y | x ⪥ᴸ y
  … | [<] | [<] x<y | [<] rewrite ⪥[>] y x x<y = ↯
  … | [≡] | [≡] x≡y | [≡] rewrite ⪥[≡] y x (◇⸢≡⸣ x≡y) = ↯
  … | [>] | [>] x>y | [>] rewrite ⪥[<] y x x>y = ↯

open Totally {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (_≺_ : relation ℓʳ A) {{_ : Irreflexive _≺_}} {{_ : Asymmetric _≺_}} {{ℭ : Totally _≺_}} where
  syntax ⪥[] _≺_ x y = x ⪥[ _≺_ ] y
  ⪥[] = Totally._⪥_ ℭ
  syntax ⪥ᴾ[] _≺_ x y = x ⪥ᴾ[ _≺_ ] y
  ⪥ᴾ[] = Totally._⪥ᴾ_ ℭ
  syntax ⪥ᴸ[] _≺_ x y = x ⪥ᴸ[ _≺_ ] y
  ⪥ᴸ[] = Totally._⪥ᴸ_ ℭ

--------------------------
-- Decidable Predicates --
--------------------------

data ‼ : Set where ✓ ✗ : ‼

𝔹↦‼ : 𝔹 → ‼
𝔹↦‼ True = ✓
𝔹↦‼ False = ✗

‼↦𝔹 : ‼ → 𝔹
‼↦𝔹 ✓ = True
‼↦𝔹 ✗ = False

if[‼]_then_else_ : ∀ {ℓ} {A : Set ℓ} → ‼ → A → A → A
if[‼] ✓ then x else _ = x
if[‼] ✗ then _ else x = x

data ✓‼ : ‼ → Set where
  instance
    ↯‼ : ✓‼ ✓
data ✗‼ : ‼ → Set where
  instance
    ↯‼ : ✗‼ ✗

data ¡ᴾ[_] {ℓ ℓʳ} {A : Set ℓ} (P : predicate ℓʳ A) (x : A) : Set ℓʳ where
  ✓ : P x → ¡ᴾ[ P ] x
  ✗ : ¬ (P x) → ¡ᴾ[ P ] x

data ¡ᴸ[_]_‖[_,_] {ℓ ℓʳ} {A : Set ℓ} (P : predicate ℓʳ A) (x : A) : ‼ → ¡ᴾ[ P ] x → Set ℓʳ where
  ✓ : ∀ {E : P x} → ¡ᴸ[ P ] x ‖[ ✓ , ✓ E ]
  ✗ : ∀ {E : ¬ (P x)} → ¡ᴸ[ P ] x ‖[ ✗ , ✗ E ]

record DecPred {ℓ ℓʳ} {A : Set ℓ} (P : predicate ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    ¿ : A → ‼
    ¿ᴾ : ∀ x → ¡ᴾ[ P ] x
    ¿ᴸ : ∀ x → ¡ᴸ[ P ] x ‖[ ¿ x , ¿ᴾ x ]
open DecPred {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (P : predicate ℓʳ A) {{ℭ : DecPred P}} where
  ¿[_] = DecPred.¿ ℭ
  ¿ᴾ[_] = DecPred.¿ᴾ ℭ
  ¿ᴸ[_] = DecPred.¿ᴸ ℭ

module _ {ℓ ℓʳ} {A : Set ℓ} {P : predicate ℓʳ A} {x : A} {{_ : DecPred P}} where
  ↯✓pred : {{_ : ✓‼ (¿[ P ] x)}} → P x
  ↯✓pred {{_}} with ¿[ P ] x | ¿ᴾ[ P ] x | id (¿ᴸ[ P ] x)
  ↯✓pred {{↯‼}} | ✓ | ✓ Px | ✓ = Px

  ↯✗pred : {{_ : ✗‼ (¿[ P ] x)}} → ¬ (P x)
  ↯✗pred {{_}} with ¿[ P ] x | ¿ᴾ[ P ] x | id (¿ᴸ[ P ] x)
  ↯✗pred {{↯‼}} | ✗ | ✗ ¬Px | ✗ = ¬Px

-------------------------
-- Decidable Relations --
-------------------------

syntax ‼ᴾ[] _≼_ x y = x ‼ᴾ[ _≼_ ] y
data ‼ᴾ[] {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) (x y : A) : Set ℓʳ where
  ✓ : x ≼ y → x ‼ᴾ[ _≼_ ] y
  ✗ : ¬ (x ≼ y) → x ‼ᴾ[ _≼_ ] y

if[‼ᴾ]_then_else_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {_≼_ : relation ℓ₁ A} {x y} → x ‼ᴾ[ _≼_ ] y → B → B → B
if[‼ᴾ] ✓ _ then x else _ = x
if[‼ᴾ] ✗ _ then _ else x = x

data is✓[‼ᴾ] {ℓ ℓʳ} {A : Set ℓ} {_≼_ : relation ℓʳ A} {x y} : predicate ℓʳ (x ‼ᴾ[ _≼_ ] y) where 
  ✓ : ∀ {P : x ≼ y} → is✓[‼ᴾ] (✓ P)

data is✗[‼ᴾ] {ℓ ℓʳ} {A : Set ℓ} {_≼_ : relation ℓʳ A} {x y} : predicate ℓʳ (x ‼ᴾ[ _≼_ ] y) where 
  ✗ : ∀ {P : ¬ (x ≼ y)} → is✗[‼ᴾ] (✗ P)

syntax ‼ᴸ[] _≼_ x y r rᴾ = x ‼ᴸ[ _≼_ ] y ‖[ r , rᴾ ]
data ‼ᴸ[] {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) (x y : A) : ‼ → x ‼ᴾ[ _≼_ ] y → Set ℓʳ where
  ✓ : ∀ {E : x ≼ y} → x ‼ᴸ[ _≼_ ] y ‖[ ✓ , ✓ E ]
  ✗ : ∀ {E : ¬ (x ≼ y)} → x ‼ᴸ[ _≼_ ] y ‖[ ✗ , ✗ E ]

record DecRel {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) : Set (ℓ ⊔ᴸ ℓʳ) where
  field
    _⁇_ : A → A → ‼
    _⁇ᴾ_ : ∀ x y → x ‼ᴾ[ _≼_ ] y
    _⁇ᴸ_ : ∀ x y → x ‼ᴸ[ _≼_ ] y ‖[ x ⁇ y , x ⁇ᴾ y ]
  _⁇ᴮ_ : A → A → 𝔹
  _⁇ᴮ_ = ‼↦𝔹 ∘∘ _⁇_
  ⁇ᴾ/is✓ : ∀ {x y} → x ≼ y → is✓[‼ᴾ] (x ⁇ᴾ y)
  ⁇ᴾ/is✓ {x} {y} ≼₁ with x ⁇ᴾ y
  … | ✓ ≼₂ = ✓
  … | ✗ ¬≼ = exfalso (¬≼ ≼₁)
  ⁇ᴾ/is✗ : ∀ {x y} → ¬ (x ≼ y) → is✗[‼ᴾ] (x ⁇ᴾ y)
  ⁇ᴾ/is✗ {x} {y} ¬≼₁ with x ⁇ᴾ y
  … | ✓ ≼₁ = exfalso (¬≼₁ ≼₁)
  … | ✗ ¬≼₂ = ✗
  
open DecRel {{…}} public
module _ {ℓ ℓʳ} {A : Set ℓ} (_≼_ : relation ℓʳ A) {{ℭ : DecRel _≼_}} where
  syntax ⁇[] _≼_ x y = x ⁇[ _≼_ ] y
  ⁇[] = DecRel._⁇_ ℭ
  syntax ⁇ᴾ[] _≼_ x y = x ⁇ᴾ[ _≼_ ] y
  ⁇ᴾ[] = DecRel._⁇ᴾ_ ℭ
  syntax ⁇ᴸ[] _≼_ x y = x ⁇ᴸ[ _≼_ ] y
  ⁇ᴸ[] = DecRel._⁇ᴸ_ ℭ

module _ {ℓ ℓʳ} {A : Set ℓ} {_≼_ : relation ℓʳ A} {x y : A} {{_ : DecRel _≼_}} where
  ↯✓rel : ∀ {{R : ✓‼ (x ⁇[ _≼_ ] y)}} → x ≼ y
  ↯✓rel {{_}} with x ⁇[ _≼_ ] y | x ⁇ᴾ[ _≼_ ] y | id (x ⁇ᴸ[ _≼_ ] y)
  ↯✓rel {{R = ↯‼}} | ✓ | ✓ xRy | ✓ = xRy
  
  ↯✗rel : ∀ {{R : ✗‼ (x ⁇[ _≼_ ] y)}} → ¬ (x ≼ y)
  ↯✗rel {{_}} with x ⁇[ _≼_ ] y | x ⁇ᴾ[ _≼_ ] y | id (x ⁇ᴸ[ _≼_ ] y)
  ↯✗rel {{↯‼}} | ✗ | ✗ ¬xRy | ✗ = ¬xRy

--------------------------
-- Intensional Equality --
--------------------------

record IEq {ℓ} (A : Set ℓ) : Set (↑ᴸ ℓ) where
  infix 14 _≍_
  infix 14 _≭_
  field
    _≍_ : relation ℓ A
    sound[≍] : ∀ {x y} → x ≍ y → x ≡ y
    complete[≍] : ∀ {x y} → x ≡ y → x ≍ y
    _≭_ : relation ℓ A
    sound[≭] : ∀ {x y} → x ≭ y → ¬ (x ≡ y)
open IEq {{…}} public
module _ {ℓ} (A : Set ℓ) {{ℭ : IEq A}} where
  ≍[_] = IEq._≍_ ℭ
  ≭[_] = IEq._≭_ ℭ
  sound[≍][_] = IEq.sound[≍] ℭ
  complete[≍][_] = IEq.complete[≍] ℭ
  sound[≭][_] = IEq.sound[≭] ℭ

------------------
-- Decidability --
------------------

record DecEq {ℓ} (A : Set ℓ) : Set ℓ where
  field
    {{DecRel[≡]}} : DecRel ≡[ A ]
  open DecRel DecRel[≡] public using () renaming
    ( _⁇_ to _⁇[≡]_
    ; _⁇ᴾ_ to _⁇ᴾ[≡]_
    ; _⁇ᴮ_ to _⁇ᴮ[≡]_
    )
open DecEq {{…}} public

record DecIEq {ℓ} (A : Set ℓ) {{_ : IEq A}} : Set ℓ where
  field
    {{DecRel[≍]}} : DecRel ≍[ A ]
  open DecRel DecRel[≍] public using () renaming
    ( _⁇_ to _⁇[≍]_
    ; _⁇ᴾ_ to _⁇[≍]ᴾ_
    ; _⁇ᴸ_ to _⁇[≍]ᴸ_
    )
open DecIEq {{…}} public

module _ {ℓ ℓʳ} {A : Set ℓ}
  (_≼_ : relation ℓʳ A) {{_ : Reflexive _≼_}} {{_ : Transitive _≼_}}
  (_≺_ : relation ℓʳ A) {{_ : Irreflexive _≺_}} {{_ : Asymmetric _≺_}} {{_ : Totally _≺_}} {{_ : Strict _≼_ _≺_}}
  where
  syntax ⁇[≡]/⪥[] _≼_ _≺_ x y = x ⁇[≡]/⪥[ _≼_ , _≺_ ] y
  syntax ⁇ᴾ[≡]/⪥[] _≼_ _≺_ x y = x ⁇ᴾ[≡]/⪥[ _≼_ , _≺_ ] y
  syntax ⁇ᴸ[≡]/⪥[] _≼_ _≺_ x y = x ⁇ᴸ[≡]/⪥[ _≼_ , _≺_ ] y
  syntax ⁇[≤]/⪥[] _≼_ _≺_ x y = x ⁇[≤]/⪥[ _≼_ , _≺_ ] y
  syntax ⁇ᴾ[≤]/⪥[] _≼_ _≺_ x y = x ⁇ᴾ[≤]/⪥[ _≼_ , _≺_ ] y
  syntax ⁇ᴸ[≤]/⪥[] _≼_ _≺_ x y = x ⁇ᴸ[≤]/⪥[ _≼_ , _≺_ ] y
  syntax ⁇[<]/⪥[] _≼_ _≺_ x y = x ⁇[<]/⪥[ _≼_ , _≺_ ] y
  syntax ⁇ᴾ[<]/⪥[] _≼_ _≺_ x y = x ⁇ᴾ[<]/⪥[ _≼_ , _≺_ ] y
  syntax ⁇ᴸ[<]/⪥[] _≼_ _≺_ x y = x ⁇ᴸ[<]/⪥[ _≼_ , _≺_ ] y
  ⁇[≡]/⪥[] : A → A → ‼
  ⁇[≡]/⪥[] x y with x ⪥[ _≺_ ] y
  … | [<] = ✗
  … | [≡] = ✓
  … | [>] = ✗
  ⁇ᴾ[≡]/⪥[] : ∀ (x y : A) → x ‼ᴾ[ _≡_ ] y
  ⁇ᴾ[≡]/⪥[] x y with x ⪥ᴾ[ _≺_ ] y
  … | [<] x<y = ✗ $ λ x≡y → ¬xRx[≡] x≡y x<y
  … | [≡] x≡y = ✓ x≡y
  … | [>] y<x = ✗ $ λ x≡y → ¬xRx[≡] (◇⸢≡⸣ x≡y) y<x
  ⁇ᴸ[≡]/⪥[] : ∀ (x y : A) → x ‼ᴸ[ _≡_ ] y ‖[ ⁇[≡]/⪥[] x y , ⁇ᴾ[≡]/⪥[] x y ]
  ⁇ᴸ[≡]/⪥[] x y with x ⪥[ _≺_ ] y | x ⪥ᴾ[ _≺_ ] y | id (x ⪥ᴸ[ _≺_ ] y)
  … | [<] | [<] _ | [<] = ✗
  … | [≡] | [≡] _ | [≡] = ✓
  … | [>] | [>] _ | [>] = ✗
  ⁇[≤]/⪥[] : A → A → ‼
  ⁇[≤]/⪥[] x y with x ⪥[ _≺_ ] y
  … | [<] = ✓
  … | [≡] = ✓
  … | [>] = ✗
  ⁇ᴾ[≤]/⪥[] : ∀ (x y : A) → x ‼ᴾ[ _≼_ ] y
  ⁇ᴾ[≤]/⪥[] x y with x ⪥ᴾ[ _≺_ ] y
  … | [<] x<y = ✓ $ weaken[≺] x<y
  … | [≡] x≡y = ✓ $ xRx[≡] x≡y
  … | [>] y<x = ✗ $ strict[≺] y<x
  ⁇ᴸ[≤]/⪥[] : ∀ (x y : A) → x ‼ᴸ[ _≼_ ] y ‖[ ⁇[≤]/⪥[] x y , ⁇ᴾ[≤]/⪥[] x y ]
  ⁇ᴸ[≤]/⪥[] x y with x ⪥[ _≺_ ] y | x ⪥ᴾ[ _≺_ ] y | id (x ⪥ᴸ[ _≺_ ] y)
  … | [<] | [<] _ | [<] = ✓
  … | [≡] | [≡] _ | [≡] = ✓
  … | [>] | [>] _ | [>] = ✗
  ⁇[<]/⪥[] : A → A → ‼
  ⁇[<]/⪥[] x y with x ⪥[ _≺_ ] y
  … | [<] = ✓
  … | [≡] = ✗
  … | [>] = ✗
  ⁇ᴾ[<]/⪥[] : ∀ (x y : A) → x ‼ᴾ[ _≺_ ] y
  ⁇ᴾ[<]/⪥[] x y with x ⪥ᴾ[ _≺_ ] y
  … | [<] x<y = ✓ x<y
  … | [≡] x≡y = ✗ $ ¬xRx[≡] x≡y
  … | [>] y<x = ✗ $ ¬◇ y<x
  ⁇ᴸ[<]/⪥[] : ∀ (x y : A) → x ‼ᴸ[ _≺_ ] y ‖[ ⁇[<]/⪥[] x y , ⁇ᴾ[<]/⪥[] x y ]
  ⁇ᴸ[<]/⪥[] x y with x ⪥[ _≺_ ] y | x ⪥ᴾ[ _≺_ ] y | id (x ⪥ᴸ[ _≺_ ] y)
  … | [<] | [<] _ | [<] = ✓
  … | [≡] | [≡] _ | [≡] = ✗
  … | [>] | [>] _ | [>] = ✗

---------------
-- Instances --
---------------

instance
  Reflexive[≡] : ∀ {ℓ} {A : Set ℓ} → Reflexive (_≡_ {A = A})
  Reflexive[≡] = record { xRx = xRx⸢≡⸣ }
  Transitive[≡] : ∀ {ℓ} {A : Set ℓ} → Transitive (_≡_ {A = A})
  Transitive[≡] = record { _⊚_ = _⊚⸢≡⸣_ }
  Symmetric[≡] : ∀ {ℓ} {A : Set ℓ} → Symmetric (_≡_ {A = A})
  Symmetric[≡] = record { ◇ = ◇⸢≡⸣ }
