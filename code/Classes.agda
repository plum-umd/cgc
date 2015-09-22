module Classes where

open import Core
open import Relations

record Additive {𝓁} (A : Set 𝓁) : Set 𝓁 where
  infixr 5 _+_
  field
    zero : A
    _+_ : A → A → A
    left-unit[+] : ∀ x → zero + x ≡ x
    right-unit[+] : ∀ x → x + zero ≡ x
    associativity[+] : ∀ x y z → (x + y) + z ≡ x + y + z
open Additive {{...}} public

record Monoid {𝓁} (A : Set 𝓁) : Set 𝓁 where
  infixr 5 _++_
  field
    null : A
    _++_ : A → A → A
    left-unit[++] : ∀ x → null ++ x ≡ x
    right-unit[++] : ∀ x → x ++ null ≡ x
    associativity[++] : ∀ x y z → (x ++ y) ++ z ≡ x ++ y ++ z
open Monoid {{...}} public

record Functor {𝓁} (F : Set 𝓁 → Set 𝓁) : Set (sucˡ 𝓁) where
  field
    map : ∀ {A B : Set 𝓁} → (A → B) → F A → F B
    unit[map] : ∀ {A : Set 𝓁} (t : F A) → map id t ≡ t
    homomorphic[map] : ∀ {A B C : Set 𝓁} (g : B → C) (f : A → B) (t : F A) → map (g ∘ f) t ≡ (map g ∘ map f) t
open Functor {{...}} public

record FiniteSet {𝓁} (F : Set 𝓁 → Set 𝓁) : Set (sucˡ 𝓁) where
  infix  8 _∈_
  infixr 5 _∪_
  infix  8 _⊆_
  field
    _∈_ : ∀ {A : Set 𝓁} → A → F A → Set 𝓁
    single : ∀ {A : Set 𝓁} → A → F A
    _∪_ : ∀ {A : Set 𝓁} → F A → F A → F A
    x∈single : ∀ {A : Set 𝓁} (x : A) → x ∈ single x
    x∈xs : ∀ {A : Set 𝓁} (x : A) (xs ys : F A) → x ∈ xs → x ∈ (xs ∪ ys)
    x∈ys : ∀ {A : Set 𝓁} (x : A) (xs ys : F A) → x ∈ ys → x ∈ (xs ∪ ys)
    x∈xs∪ys→⨄ : ∀ {A : Set 𝓁} (x : A) (xs ys : F A) → x ∈ (xs ∪ ys) → x ∈ xs ⨄ x ∈ ys
  _⊆_ : ∀ {A : Set 𝓁} → F A → F A → Set 𝓁
  X ⊆ Y = ∀ x → x ∈ X → x ∈ Y
open FiniteSet {{...}} public

record Reflexive {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁') where
  field
    xRx : reflexive _R_
  xRx[≡] : reflexive[ _≡_ ] _R_
  xRx[≡] ↯ = xRx
open Reflexive {{...}} public

record Reflexive[_] {𝓁 𝓁' 𝓁''} {A : Set 𝓁} (_~_ : relation 𝓁' A) (_R_ : relation 𝓁'' A) : Set (𝓁 ⊔ˡ 𝓁' ⊔ˡ 𝓁'') where
  field
    xRx[] : reflexive[ _~_ ] _R_
open Reflexive[_] {{...}} public

xRx[_] : ∀ {𝓁 𝓁' 𝓁''} {A : Set 𝓁} (_~_ : relation 𝓁' A) {_R_ : relation 𝓁'' A} {{Refl : Reflexive[ _~_ ] _R_}} {x y} → x ~ y → x R y
xRx[ _~_ ] = xRx[]

record Transitive {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁') where
  infixr 9 _⌾_
  field
    _⌾_ : transitive _R_
open Transitive {{...}} public

record Symmetric {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁') where
  field
    ◇ : symmetric _R_
open Symmetric {{...}} public

record Symmetric[_] {𝓁 𝓁' 𝓁''} {A : Set 𝓁} (_REV_ : relation 𝓁' A) (_R_ : relation 𝓁'' A) : Set (𝓁 ⊔ˡ 𝓁' ⊔ˡ 𝓁'') where
  field
    ◇→[] : symmetric→[ _REV_ ] _R_
    ◇←[] : symmetric←[ _REV_ ] _R_
open Symmetric[_] {{...}} public

record Antisymmetric {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁') where
  field
    ⋈ : antisymmetric _R_
open Antisymmetric {{...}} public

record Antisymmetric[_] {𝓁 𝓁' 𝓁''} {A : Set 𝓁} (_~_ : relation 𝓁' A) (_R_ : relation 𝓁'' A) : Set (𝓁 ⊔ˡ 𝓁' ⊔ˡ 𝓁'') where
  field
    ⋈[] : ∀ {x y} → x R y → y R x → x ~ y
open Antisymmetric[_] {{...}} public

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

record TotalOrder {𝓁 𝓁'} 𝓁'' (A : Set 𝓁) (_~_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁' ⊔ˡ sucˡ 𝓁'') where
  infix 8 _≤_
  infix 8 _≥_
  infix 8 _<_
  infix 8 _>_
  infix 9 _⌾⸢≤⸣_
  field
    _≤_ : relation 𝓁'' A
    _⋚_ : dec-total-order _~_ _≤_
    {{Reflexive[][≤]}} : Reflexive[ _~_ ] _≤_
    {{Transitive[≤]}} : Transitive _≤_
    {{Antisymmetric[][≤]}} : Antisymmetric[ _~_ ] _≤_
  _≥_ : relation 𝓁'' A
  _≥_ = flip _≤_
  _<_ : relation 𝓁'' A
  x < y = x ≤ y × not (y ≤ x)
  _>_ : relation 𝓁'' A
  x > y = x ≥ y × not (y ≥ x)
  xRx[]⸢≤⸣ : reflexive[ _~_ ] _≤_
  xRx[]⸢≤⸣ = xRx[] {{Reflexive[][≤]}}
  _⌾⸢≤⸣_ : transitive _≤_
  _⌾⸢≤⸣_ = _⌾_ {{Transitive[≤]}}
  ⋈[]⸢≤⸣ : antisymmetric[ _~_ ] _≤_
  ⋈[]⸢≤⸣ = ⋈[] {{Antisymmetric[][≤]}}
open TotalOrder {{...}} public

record RelDec {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) : Set (𝓁 ⊔ˡ 𝓁') where
  field
    dec[] : rel-dec _R_
open RelDec {{...}} public

dec[_] : ∀ {𝓁 𝓁'} {A : Set 𝓁} (_R_ : relation 𝓁' A) {{RD : RelDec _R_}} → rel-dec _R_
dec[ _R_ ] = dec[]

instance
  Reflexive[≡] : ∀ {𝓁} {A : Set 𝓁} → Reflexive (_≡_ {A = A})
  Reflexive[≡] = record { xRx = xRx⸢≡⸣ }
  Transitive[≡] : ∀ {𝓁} {A : Set 𝓁} → Transitive (_≡_ {A = A})
  Transitive[≡] = record { _⌾_ = _⌾⸢≡⸣_ }
  Symmetric[≡] : ∀ {𝓁} {A : Set 𝓁} → Symmetric (_≡_ {A = A})
  Symmetric[≡] = record { ◇ = ◇⸢≡⸣ }

≡-PreOrder : ∀ {𝓁} {A : Set 𝓁} → PreOrder 𝓁 A
≡-PreOrder = record { _⊴_ = _≡_ }

-- record _⊴⊵_ {𝓁 𝓁'} {A : Set 𝓁} {{Pre : PreOrder 𝓁' A}} (x y : A) : Set 𝓁' where
--   constructor mk[⊴⊵]
--   field
--     xRy : x ⊴ y
--     yRx : y ⊴ x
-- 
-- instance
--   Reflexive[⊴⊵] : ∀ {𝓁 𝓁'} {A : Set 𝓁} {{Pre : PreOrder 𝓁' A}} → Reflexive _⊴⊵_
--   Reflexive[⊴⊵] = record { xRx = record { xRy = xRx⸢⊴⸣ ; yRx = xRx⸢⊴⸣ } }
--   Symmetric[⊴⊵] : ∀ {𝓁 𝓁'} {A : Set 𝓁} {{Pre : PreOrder 𝓁' A}} → Symmetric _⊴⊵_
--   Symmetric[⊴⊵] = record { ◇ = λ { (mk[⊴⊵] xRy yRx) → mk[⊴⊵] yRx xRy }}
--   Transitive[⊴⊵] : ∀ {𝓁 𝓁'} {A : Set 𝓁} {{Pre : PreOrder 𝓁' A}} → Transitive _⊴⊵_
--   Transitive[⊴⊵] = record { _⌾_ = λ { (mk[⊴⊵] yRz zRy) (mk[⊴⊵] xRy yRx) → mk[⊴⊵] (yRz ⌾⸢⊴⸣ xRy) (yRx ⌾⸢⊴⸣ zRy) }}
--   Reflexive[⊴⊵][⊴] : ∀ {𝓁 𝓁'} {A : Set 𝓁} {{Pre : PreOrder 𝓁' A}} → Reflexive[ _⊴⊵_ ] _⊴_
--   Reflexive[⊴⊵][⊴] = record { xRx[] = _⊴⊵_.xRy }
--   Antisymmetric[⊴⊵][⊴] : ∀ {𝓁 𝓁'} {A : Set 𝓁} {{Pre : PreOrder 𝓁' A}} → Antisymmetric[ _⊴⊵_ ] _⊴_
--   Antisymmetric[⊴⊵][⊴] = record { ⋈[] = mk[⊴⊵] }
-- 
-- ⊴⊵-Equivalence : ∀ {𝓁 𝓁'} {A : Set 𝓁} {{Pre : PreOrder 𝓁' A}} → Equivalence 𝓁' A
-- ⊴⊵-Equivalence = record { _≈_ = _⊴⊵_ }
-- ⊴⊵-PartialOrder : ∀ {𝓁 𝓁'} {A : Set 𝓁} {{Pre : PreOrder 𝓁' A}} → PartialOrder 𝓁' A _⊴⊵_
-- ⊴⊵-PartialOrder {{PO}} = record
--   { _⊑_ = _⊴_
--   ; Reflexive[][⊑] = Reflexive[⊴⊵][⊴]
--   ; Transitive[⊑] = Transitive[⊴]
--   ; Antisymmetric[][⊑] = Antisymmetric[⊴⊵][⊴]
--   }
