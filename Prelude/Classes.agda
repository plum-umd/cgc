module Prelude.Classes where

open import Prelude.Core
open import Prelude.Relations

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
open Additive {{...}} public

record Subtractive {ℓ} (A : Set ℓ) {{X : Additive A}} : Set ℓ where
  infix 23 _-_
  infixr 60 ⁻_
  field
    _-_ : A → A → A
    correct[-] : ∀ x y → y + (x - y) ≡ x
  ⁻_ : A → A
  ⁻ x = zero {{X}} - x
open Subtractive {{...}} public

record Subtractive/OK {ℓ} (A : Set ℓ) : Set (↑ᴸ ℓ) where
  field
    ok[_-_] : A → A → Set ℓ
open Subtractive/OK {{...}} public

record Subtractive/P {ℓ} (A : Set ℓ) {{_ : Additive A}} {{_ : Subtractive/OK A}} : Set ℓ where
  infix 23 _-_‖_
  field
    ok[x-x] : ∀ (x : A) → ok[ x - x ]
    _-_‖_ : ∀ x y → ok[ x - y ] → A
    correct[-‖] : ∀ x y (ok[x-y] : ok[ x - y ]) → y + (x - y ‖ ok[x-y]) ≡ x
open Subtractive/P {{...}} public

record Multiplicative {ℓ} (A : Set ℓ) {{_ : Additive A}} : Set ℓ where
  infixr 24 _×_
  field
    one : A
    _×_ : A → A → A
    left-zero[×] : ∀ x → zero × x ≡ zero
    right-zero[×] : ∀ x → x × zero ≡ zero
    left-unit[×] : ∀ x → one × x ≡ x
    right-unit[×] : ∀ x → x × one ≡ x
    associative[×] : ∀ x y z → (x × y) × z ≡ x × y × z
    commutative[×] : ∀ x y → x × y ≡ y × x
    distributive[×] : ∀ x y z → (x + y) × z ≡ x × z + y × z
open Multiplicative {{...}} public

record DivMod {ℓ} (A : Set ℓ) {{_ : Additive A}} {{_ : Multiplicative A}} : Set ℓ where
  infix  25 _/%_
  field
    _/%_ : A → A → A ∧ A
    correct[/%] : ∀ x y → let q , r = x /% y in y × q + r ≡ x
open DivMod {{...}} public 

record DivMod/OK {ℓ} (A : Set ℓ) : Set (↑ᴸ ℓ) where
  field
    ok[_/%_] : A → A → Set ℓ
open DivMod/OK {{...}} public

record DivMod/P {ℓ} (A : Set ℓ) {{_ : Additive A}} {{_ : Multiplicative A}} {{_ : DivMod/OK A}} : Set ℓ where
  infix  25 _/%_‖_
  field
    _/%_‖_ : ∀ x y → ok[ x /% y ] → A ∧ A
    correct[/%‖] : ∀ x y (ok[x/%y] : ok[ x /% y ]) → let q , r = x /% y ‖ ok[x/%y] in y × q + r ≡ x
open DivMod/P {{...}} public

module _ {ℓ} {A : Set ℓ} {{_ : Additive A}} {{_ : Multiplicative A}} {{_ : DivMod/OK A}} {{_ : DivMod/P A}} where
  infix 25 _/_‖_
  _/_‖_ : ∀ (x y : A) → ok[ x /% y ] → A
  x / y ‖ ok = π₁ (x /% y ‖ ok)
  infix 23 _%_‖_
  _%_‖_ : ∀ (x y : A) → ok[ x /% y ] → A
  x % y ‖ ok = π₂ (x /% y ‖ ok)

----------------
-- Finite Set --
----------------

record FiniteSet {ℓ} (F : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  infix  14 _∈_
  infixr 22 _∪_
  infix  14 _⊆_
  field
    _∈_ : ∀ {A : Set ℓ} → A → F A → Set ℓ
    single : ∀ {A : Set ℓ} → A → F A
    _∪_ : ∀ {A : Set ℓ} → F A → F A → F A
    ∈single : ∀ {A : Set ℓ} (x : A) → x ∈ single x
    ∈∪/IL : ∀ {A : Set ℓ} (x : A) (xs ys : F A) → x ∈ xs → x ∈ (xs ∪ ys)
    ∈∪/IR : ∀ {A : Set ℓ} (y : A) (xs ys : F A) → y ∈ ys → y ∈ (xs ∪ ys)
    ∈∪/E : ∀ {A : Set ℓ} (z : A) (xs ys : F A) → z ∈ (xs ∪ ys) → z ∈ xs ∨ z ∈ ys
  _⊆_ : ∀ {A : Set ℓ} → F A → F A → Set ℓ
  X ⊆ Y = ∀ {x} → x ∈ X → x ∈ Y
open FiniteSet {{...}} public

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
open Monoid {{...}} public

-------------
-- Functor --
-------------

record Functor {ℓ} (F : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  field
    map : ∀ {A B : Set ℓ} → (A → B) → F A → F B
    unit[map] : ∀ {A : Set ℓ} (t : F A) → map id t ≡ t
    homomorphic[map] : ∀ {A B C : Set ℓ} (g : B → C) (f : A → B) (t : F A) → map (g ∘ f) t ≡ (map g ∘ map f) t
open Functor {{...}} public

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
     ‣ let (x , y) = xy in
       f x y
open Monad {{...}} public

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

record Injective {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ᴸ ℓ₂) where
  field
    injective : ∀ {x y} → f x ≡ f y → x ≡ y
open Injective {{...}} public

record Reflexive {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) : Set (ℓ ⊔ᴸ ℓ') where
  field
    xRx : reflexive _R_
  xRx[≡] : reflexive[ _≡_ ] _R_
  xRx[≡] ↯ = xRx
open Reflexive {{...}} public

record Transitive {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) : Set (ℓ ⊔ᴸ ℓ') where
  infixr 30 _⊚_
  field
    _⊚_ : transitive _R_
open Transitive {{...}} public

record Symmetric {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) : Set (ℓ ⊔ᴸ ℓ') where
  field
    ◇ : symmetric _R_
open Symmetric {{...}} public

record Antisymmetric {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) : Set (ℓ ⊔ᴸ ℓ') where
  field
    ⋈ : antisymmetric _R_
open Antisymmetric {{...}} public

record Category {ℓ ℓ'} {A : Set ℓ} (_↝_ : A → A → Set ℓ') : Set (ℓ ⊔ᴸ ℓ') where
  field
    {{Reflexive[↝]}} : Reflexive _↝_
    {{Transitive[↝]}} : Transitive _↝_
    left-unit : ∀ {x y} (f : x ↝ y) → xRx ⊚ f ≡ f
    right-unit : ∀ {x y} (f : x ↝ y) → f ⊚ xRx ≡ f
    associative : ∀ {w x y z} (h : y ↝ z) (g : x ↝ y) (f : w ↝ x) → (h ⊚ g) ⊚ f ≡ h ⊚ g ⊚ f
open Category {{...}}

record PreOrder {ℓ} ℓ' (A : Set ℓ) : Set (ℓ ⊔ᴸ ↑ᴸ ℓ') where
  infix 14 _≼_
  infix 14 _≽_
  infixr 30 _⊚⸢≼⸣_
  field
    _≼_ : relation ℓ' A
    {{Reflexive[≼]}} : Reflexive _≼_
    {{Transitive[≼]}} : Transitive _≼_
  _≽_ : relation ℓ' A
  _≽_ = flip _≼_
  xRx⸢≼⸣ : reflexive _≼_
  xRx⸢≼⸣ = xRx {{Reflexive[≼]}}
  _⊚⸢≼⸣_ : transitive _≼_
  _⊚⸢≼⸣_ = _⊚_ {{Transitive[≼]}}
open PreOrder {{...}} public

record PartialOrder {ℓ} ℓ' (A : Set ℓ)  : Set (ℓ ⊔ᴸ ↑ᴸ ℓ') where
  infix 14 _⊑_
  infix 14 _⊒_
  infixr 30 _⊚⸢⊑⸣_
  field
    _⊑_ : relation ℓ' A
    {{Reflexive[⊑]}} : Reflexive _⊑_
    {{Transitive[⊑]}} : Transitive _⊑_
    {{Antisymmetric[⊑]}} : Antisymmetric _⊑_
  _⊒_ : relation ℓ' A
  _⊒_ = flip _⊑_
  xRx⸢⊑⸣ : reflexive _⊑_
  xRx⸢⊑⸣ = xRx {{Reflexive[⊑]}}
  ⋈⸢⊑⸣ : antisymmetric _⊑_
  ⋈⸢⊑⸣ = ⋈ {{Antisymmetric[⊑]}}
  _⊚⸢⊑⸣_ : transitive _⊑_
  _⊚⸢⊑⸣_ = _⊚_ {{Transitive[⊑]}}
open PartialOrder {{...}} public  

record TotalOrder {ℓ} ℓ' (A : Set ℓ) : Set (ℓ ⊔ᴸ ↑ᴸ ℓ') where
  infix 14 _≤_
  infix 14 _≥_
  infix 14 _<_
  infix 14 _>_
  infixr 30 _⊚⸢≤⸣_
  field
    _≤_ : relation ℓ' A
    _<_ : relation ℓ' A
    correct[<] : ∀ {x y} → x < y ↔ x ≤ y ∧ not (y ≤ x)
    _⋚_ : dec-total-order _≡_ _≤_
    {{Reflexive[≤]}} : Reflexive _≤_
    {{Transitive[≤]}} : Transitive _≤_
    {{Antisymmetric[≤]}} : Antisymmetric _≤_
  _≥_ : relation ℓ' A
  _≥_ = flip _≤_
  _>_ : relation ℓ' A
  _>_ = flip _<_
  xRx⸢≤⸣ : reflexive _≤_
  xRx⸢≤⸣ = xRx {{Reflexive[≤]}}
  _⊚⸢≤⸣_ : transitive _≤_
  _⊚⸢≤⸣_ = _⊚_ {{Transitive[≤]}}
  ⋈⸢≤⸣ : antisymmetric _≤_
  ⋈⸢≤⸣ = ⋈ {{Antisymmetric[≤]}}
open TotalOrder {{...}} public

record Equivalence {ℓ} ℓ' (A : Set ℓ) : Set (ℓ ⊔ᴸ ↑ᴸ ℓ') where
  infix 14 _≈_
  infixr 30 _⊚⸢≈⸣_
  field
    _≈_ : relation ℓ' A
    {{Reflexive[≈]}} : Reflexive _≈_
    {{Symmetric[≈]}} : Symmetric _≈_
    {{Transitive[≈]}} : Transitive _≈_
  xRx⸢≈⸣ : reflexive _≈_
  xRx⸢≈⸣ = xRx {{Reflexive[≈]}}
  ◇⸢≈⸣ : symmetric _≈_
  ◇⸢≈⸣ = ◇ {{Symmetric[≈]}}
  _⊚⸢≈⸣_ : transitive _≈_
  _⊚⸢≈⸣_ = _⊚_ {{Transitive[≈]}}
open Equivalence {{...}} public

-----------------------------------
-- Relations with non-≡ equality --
-----------------------------------

record Injective[_,_] {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ} {A : Set ℓ₁} {_R₁_ : relation ℓ₁ʳ A} {B : Set ℓ₂} {_R₂_ : relation ℓ₂ʳ B} (f : A → B) : Set (ℓ₁ ⊔ᴸ ℓ₁ʳ ⊔ᴸ ℓ₂ ⊔ᴸ ℓ₂ʳ) where
  field
    injective[] : ∀ {x y} → f x R₂ f y → x R₁ y
open Injective[_,_] {{...}} public

record Reflexive[_] {ℓ ℓ' ℓ''} {A : Set ℓ} (_~_ : relation ℓ' A) (_R_ : relation ℓ'' A) : Set (ℓ ⊔ᴸ ℓ' ⊔ᴸ ℓ'') where
  field
    xRx[] : reflexive[ _~_ ] _R_
open Reflexive[_] {{...}} public

xRx[_] : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} (_~_ : relation ℓ' A) {_R_ : relation ℓ'' A} {{Refl : Reflexive[ _~_ ] _R_}} {x y} → x ~ y → x R y
xRx[ _~_ ] = xRx[]

record Antisymmetric[_] {ℓ ℓ' ℓ''} {A : Set ℓ} (_~_ : relation ℓ' A) (_R_ : relation ℓ'' A) : Set (ℓ ⊔ᴸ ℓ' ⊔ᴸ ℓ'') where
  field
    ⋈[] : antisymmetric[ _~_ ] _R_
open Antisymmetric[_] {{...}} public

-------------------------
-- Decidable Relations --
-------------------------

record DecRel {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) : Set (ℓ ⊔ᴸ ℓ') where
  field
    dec[] : dec-rel _R_
open DecRel {{...}} public

dec[_] : ∀ {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) {{DR : DecRel _R_}} → dec-rel _R_
dec[ _R_ ] = dec[]

↯is-rel : ∀ {ℓ ℓ'} {A : Set ℓ} {_R_ : relation ℓ' A} {x y : A} {{DR : DecRel _R_}} {{IR : is-rel (dec[ _R_ ] x y)}} → x R y
↯is-rel {x = x} {y} {{DR}} {{IR}} with dec[] {{DR}} x y
↯is-rel {{IR = ↯Rel}} | Yes xRy = xRy

↯not-rel : ∀ {ℓ ℓ'} {A : Set ℓ} {_R_ : relation ℓ' A} {x y : A} {{DR : DecRel _R_}} {{IR : not-rel (dec[ _R_ ] x y)}} → not (x R y)
↯not-rel {x = x} {y = y} {{DR}} {{IR}} with dec[] {{DR}} x y
↯not-rel {{IR = ↯Rel}} | No ¬xRy = ¬xRy

record Eq {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : A → A → 𝔹
    correct[≟] : ∀ x y → (x ≟ y ≡ True) ↔ (x ≡ y)
open Eq {{...}} public

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

PreOrder[≡] : ∀ {ℓ} {A : Set ℓ} → PreOrder ℓ A
PreOrder[≡] = record { _≼_ = _≡_ }

Equivalence[≡] : ∀ {ℓ} {A : Set ℓ} → Equivalence ℓ A
Equivalence[≡] = record { _≈_ = _≡_ }
