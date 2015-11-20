module Prelude.Classes where

open import Prelude.Core
open import Prelude.Relations

-------------
-- Monoid  --
-------------

record Monoid {𝓁} (A : Set 𝓁) : Set 𝓁 where
  infixr 5 _⧺_
  field
    null : A
    _⧺_ : A → A → A
    left-unit[⧺] : ∀ x → null ⧺ x ≡ x
    right-unit[⧺] : ∀ x → x ⧺ null ≡ x
    associative[⧺] : ∀ x y z → (x ⧺ y) ⧺ z ≡ x ⧺ y ⧺ z
open Monoid {{...}} public

record Additive {𝓁} (A : Set 𝓁) : Set 𝓁 where
  infixr 5 _+_
  field
    zero : A
    _+_ : A → A → A
    left-unit[+] : ∀ x → zero + x ≡ x
    right-unit[+] : ∀ x → x + zero ≡ x
    associative[+] : ∀ x y z → (x + y) + z ≡ x + y + z
    commutative[+] : ∀ x y → x + y ≡ y + x
open Additive {{...}} public

record Multiplicative {𝓁} (A : Set 𝓁) {{_ : Additive A}} : Set 𝓁 where
  infixr 6 _⨯_
  field
    one : A
    _⨯_ : A → A → A
    left-zero[⨯] : ∀ x → zero ⨯ x ≡ zero
    right-zero[⨯] : ∀ x → x ⨯ zero ≡ zero
    left-unit[⨯] : ∀ x → one ⨯ x ≡ x
    right-unit[⨯] : ∀ x → x ⨯ one ≡ x
    associative[⨯] : ∀ x y z → (x ⨯ y) ⨯ z ≡ x ⨯ y ⨯ z
    commutative[⨯] : ∀ x y → x ⨯ y ≡ y ⨯ x
    distributive[⨯] : ∀ x y z → (x + y) ⨯ z ≡ x ⨯ z + y ⨯ z
open Multiplicative {{...}} public

record Subtractive {𝓁} (A : Set 𝓁) {{_ : Additive A}} : Set 𝓁 where
  infix 5 _-_
  field
    _-_ : A → A → A
    correct[-] : ∀ x y → y + (x - y) ≡ x
  ⁻_ : A → A
  ⁻ x = zero - x
open Subtractive {{...}} public

record Subtractiveᵖ {𝓁} (A : Set 𝓁) {{_ : Additive A}} (ok[_-_] : A → A → Set 𝓁) : Set 𝓁 where
  infix 5 _-_‖_
  field
    ok[x-x] : ∀ x → ok[ x - x ]
    _-_‖_ : ∀ x y → ok[ x - y ] → A
    correct[-‖] : ∀ x y (ok[x-y] : ok[ x - y ]) → y + (x - y ‖ ok[x-y]) ≡ x
open Subtractiveᵖ {{...}} public

record DivMod {𝓁} (A : Set 𝓁) {{_ : Additive A}} {{_ : Multiplicative A}} : Set 𝓁 where
  infix  6 _/%_
  field
    _/%_ : A → A → A × A
    correct[/%] : ∀ x y → let q , r = x /% y in y ⨯ q + r ≡ x
open DivMod {{...}} public 

record DivModᵖ {𝓁} (A : Set 𝓁) {{_ : Additive A}} {{_ : Multiplicative A}} (ok[_/%_] : A → A → Set 𝓁) : Set 𝓁 where
  infix  6 _/%_‖_
  field
    _/%_‖_ : ∀ x y → ok[ x /% y ] → A × A
    correct[/%‖] : ∀ x y (ok[x/%y] : ok[ x /% y ]) → let q , r = x /% y ‖ ok[x/%y] in y ⨯ q + r ≡ x
open DivModᵖ {{...}} public

module _ {𝓁} {A : Set 𝓁} {{_ : Additive A}} {{_ : Multiplicative A}} {ok[_/%_] : A → A → Set 𝓁} {{_ : DivModᵖ A ok[_/%_]}} where
  infix 6 _/_‖_
  _/_‖_ : ∀ (x y : A) → ok[ x /% y ] → A
  x / y ‖ ok[x/%y] = π₁ (x /% y ‖ ok[x/%y])
  infix 6 _%_‖_
  _%_‖_ : ∀ (x y : A) → ok[ x /% y ] → A
  x % y ‖ ok[x/%y] = π₂ (x /% y ‖ ok[x/%y])

-------------
-- Functor --
-------------

record Functor {𝓁} (F : Set 𝓁 → Set 𝓁) : Set (sucˡ 𝓁) where
  field
    map : ∀ {A B : Set 𝓁} → (A → B) → F A → F B
    unit[map] : ∀ {A : Set 𝓁} (t : F A) → map id t ≡ t
    homomorphic[map] : ∀ {A B C : Set 𝓁} (g : B → C) (f : A → B) (t : F A) → map (g ∘ f) t ≡ (map g ∘ map f) t
open Functor {{...}} public

---------------
-- Relations --
---------------

record Reflexive {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁') where
  field
    xRx : reflexive _R_
  xRx[≡] : reflexive[ _≡_ ] _R_
  xRx[≡] ↯ = xRx
open Reflexive {{...}} public

record Transitive {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁') where
  infixr 9 _⌾_
  field
    _⌾_ : transitive _R_
open Transitive {{...}} public

record Symmetric {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁') where
  field
    ◇ : symmetric _R_
open Symmetric {{...}} public

record Antisymmetric {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁') where
  field
    ⋈ : antisymmetric _R_
open Antisymmetric {{...}} public

record PreOrder {𝓁} 𝓁' (A : Set 𝓁) : Set (𝓁 ⊔ˡ sucˡ 𝓁') where
  infix 8 _⊴_
  infix 8 _⊵_
  infix 9 _⌾⸢⊴⸣_
  field
    _⊴_ : relation 𝓁' A
    {{Reflexive[⊴]}} : Reflexive _⊴_
    {{Transitive[⊴]}} : Transitive _⊴_
  _⊵_ : relation 𝓁' A
  _⊵_ = flip _⊴_
  xRx⸢⊴⸣ : reflexive _⊴_
  xRx⸢⊴⸣ = xRx {{Reflexive[⊴]}}
  _⌾⸢⊴⸣_ : transitive _⊴_
  _⌾⸢⊴⸣_ = _⌾_ {{Transitive[⊴]}}
open PreOrder {{...}} public

record TotalOrder {𝓁} 𝓁' (A : Set 𝓁) : Set (𝓁 ⊔ˡ sucˡ 𝓁') where
  infix 8 _≤_
  infix 8 _≥_
  infix 8 _<_
  infix 8 _>_
  infix 9 _⌾⸢≤⸣_
  field
    _≤_ : relation 𝓁' A
    _<_ : relation 𝓁' A
    correct[<] : ∀ {x y} → x < y ↔ x ≤ y × not (y ≤ x)
    _⋚_ : dec-total-order _≡_ _≤_
    {{Reflexive[≤]}} : Reflexive _≤_
    {{Transitive[≤]}} : Transitive _≤_
    {{Antisymmetric[≤]}} : Antisymmetric _≤_
  _≥_ : relation 𝓁' A
  _≥_ = flip _≤_
  -- _<_ : relation 𝓁' A
  -- x < y = x ≤ y × not (y ≤ x)
  _>_ : relation 𝓁' A
  _>_ = flip _<_
  xRx⸢≤⸣ : reflexive _≤_
  xRx⸢≤⸣ = xRx {{Reflexive[≤]}}
  _⌾⸢≤⸣_ : transitive _≤_
  _⌾⸢≤⸣_ = _⌾_ {{Transitive[≤]}}
  ⋈⸢≤⸣ : antisymmetric _≤_
  ⋈⸢≤⸣ = ⋈ {{Antisymmetric[≤]}}
open TotalOrder {{...}} public

-----------------------------------
-- Relations with non-≡ equality --
-----------------------------------

record Reflexive[_] {𝓁 𝓁' 𝓁''} {A : Set 𝓁} (_~_ : relation 𝓁' A) (_R_ : relation 𝓁'' A) : Set (𝓁 ⊔ˡ 𝓁' ⊔ˡ 𝓁'') where
  field
    xRx[] : reflexive[ _~_ ] _R_
open Reflexive[_] {{...}} public

xRx[_] : ∀ {𝓁 𝓁' 𝓁''} {A : Set 𝓁} (_~_ : relation 𝓁' A) {_R_ : relation 𝓁'' A} {{Refl : Reflexive[ _~_ ] _R_}} {x y} → x ~ y → x R y
xRx[ _~_ ] = xRx[]

record Symmetric[_] {𝓁 𝓁' 𝓁''} {A : Set 𝓁} (_REV_ : relation 𝓁' A) (_R_ : relation 𝓁'' A) : Set (𝓁 ⊔ˡ 𝓁' ⊔ˡ 𝓁'') where
  field
    ◇→[] : symmetric→[ _REV_ ] _R_
    ◇←[] : symmetric←[ _REV_ ] _R_
open Symmetric[_] {{...}} public

record Antisymmetric[_] {𝓁 𝓁' 𝓁''} {A : Set 𝓁} (_~_ : relation 𝓁' A) (_R_ : relation 𝓁'' A) : Set (𝓁 ⊔ˡ 𝓁' ⊔ˡ 𝓁'') where
  field
    ⋈[] : ∀ {x y} → x R y → y R x → x ~ y
open Antisymmetric[_] {{...}} public

record DecRel {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁') where
  field
    dec[] : dec-rel _R_
open DecRel {{...}} public

dec[_] : ∀ {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) {{DR : DecRel _R_}} → dec-rel _R_
dec[ _R_ ] = dec[]

↯is-rel : ∀ {𝓁 𝓁'} {A : Set 𝓁} {_R_ : relation 𝓁' A} {x y : A} {{DR : DecRel _R_}} {{IR : is-rel (dec[ _R_ ] x y)}} → x R y
↯is-rel {x = x} {y} {{IR = IR}} with dec[] x y
↯is-rel {{IR = ↯Rel}} | Yes xRy = xRy
↯is-rel {{IR = ()}} | No ¬xRy

↯not-rel : ∀ {𝓁 𝓁'} {A : Set 𝓁} {_R_ : relation 𝓁' A} {x y : A} {{DR : DecRel _R_}} {{IR : not-rel (dec[ _R_ ] x y)}} → not (x R y)
↯not-rel {x = x} {y} {{IR = IR}} with dec[] x y
↯not-rel {{IR = ()}} | Yes xRy
↯not-rel {{IR = ↯Rel}} | No ¬xRy = ¬xRy

instance
  Reflexive[≡] : ∀ {𝓁} {A : Set 𝓁} → Reflexive (_≡_ {A = A})
  Reflexive[≡] = record { xRx = xRx⸢≡⸣ }
  Transitive[≡] : ∀ {𝓁} {A : Set 𝓁} → Transitive (_≡_ {A = A})
  Transitive[≡] = record { _⌾_ = _⌾⸢≡⸣_ }
  Symmetric[≡] : ∀ {𝓁} {A : Set 𝓁} → Symmetric (_≡_ {A = A})
  Symmetric[≡] = record { ◇ = ◇⸢≡⸣ }

≡-PreOrder : ∀ {𝓁} {A : Set 𝓁} → PreOrder 𝓁 A
≡-PreOrder = record { _⊴_ = _≡_ }

-- record FiniteSet {𝓁} (F : Set 𝓁 → Set 𝓁) : Set (sucˡ 𝓁) where
--   infix  8 _∈_
--   infixr 5 _∪_
--   infix  8 _⊆_
--   field
--     _∈_ : ∀ {A : Set 𝓁} → A → F A → Set 𝓁
--     single : ∀ {A : Set 𝓁} → A → F A
--     _∪_ : ∀ {A : Set 𝓁} → F A → F A → F A
--     x∈single : ∀ {A : Set 𝓁} (x : A) → x ∈ single x
--     x∈xs : ∀ {A : Set 𝓁} (x : A) (xs ys : F A) → x ∈ xs → x ∈ (xs ∪ ys)
--     x∈ys : ∀ {A : Set 𝓁} (x : A) (xs ys : F A) → x ∈ ys → x ∈ (xs ∪ ys)
--     x∈xs∪ys→⨄ : ∀ {A : Set 𝓁} (x : A) (xs ys : F A) → x ∈ (xs ∪ ys) → x ∈ xs ⨄ x ∈ ys
--   _⊆_ : ∀ {A : Set 𝓁} → F A → F A → Set 𝓁
--   X ⊆ Y = ∀ x → x ∈ X → x ∈ Y
-- open FiniteSet {{...}} public

-- record Injective {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} (f : A → B) : Set (𝓁₁ ⊔ˡ 𝓁₂) where
--   field
--     injective : ∀ {x y} → f x ≡ f y → x ≡ y
-- open Injective {{...}} public

-- record Equivalence {𝓁} 𝓁' (A : Set 𝓁) : Set (𝓁 ⊔ˡ sucˡ 𝓁') where
--   infix 8 _≈_
--   infix 9 _⌾⸢≈⸣_
--   field
--     _≈_ : relation 𝓁' A
--     {{Reflexive[≈]}} : Reflexive _≈_
--     {{Symmetric[≈]}} : Symmetric _≈_
--     {{Transitive[≈]}} : Transitive _≈_
--   xRx⸢≈⸣ : reflexive _≈_
--   xRx⸢≈⸣ = xRx {{Reflexive[≈]}}
--   ◇⸢≈⸣ : symmetric _≈_
--   ◇⸢≈⸣ = ◇ {{Symmetric[≈]}}
--   _⌾⸢≈⸣_ : transitive _≈_
--   _⌾⸢≈⸣_ = _⌾_ {{Transitive[≈]}}
-- open Equivalence {{...}} public
-- 
-- record PartialOrder {𝓁 𝓁'} 𝓁'' (A : Set 𝓁) (_~_ : relation 𝓁' A) {{Refl : Reflexive _~_}} : Set (𝓁 ⊔ˡ 𝓁' ⊔ˡ sucˡ 𝓁'') where
--   infix 8 _⊑_
--   infix 8 _⊒_
--   infix 9 _⌾⸢⊑⸣_
--   field
--     _⊑_ : relation 𝓁'' A
--     {{Reflexive[][⊑]}} : Reflexive[ _~_ ] _⊑_
--     {{Transitive[⊑]}} : Transitive _⊑_
--     {{Antisymmetric[][⊑]}} : Antisymmetric[ _~_ ] _⊑_
--   _⊒_ : relation 𝓁'' A
--   _⊒_ = flip _⊑_
--   xRx[]⸢⊑⸣ : reflexive[ _~_ ] _⊑_
--   xRx[]⸢⊑⸣ = xRx[] {{Reflexive[][⊑]}}
--   xRx⸢⊑⸣ : reflexive _⊑_
--   xRx⸢⊑⸣ = xRx[]⸢⊑⸣ xRx
--   ⋈[]⸢⊑⸣ : antisymmetric[ _~_ ] _⊑_
--   ⋈[]⸢⊑⸣ = ⋈[] {{Antisymmetric[][⊑]}}
--   _⌾⸢⊑⸣_ : transitive _⊑_
--   _⌾⸢⊑⸣_ = _⌾_ {{Transitive[⊑]}}
-- open PartialOrder {{...}} public  
