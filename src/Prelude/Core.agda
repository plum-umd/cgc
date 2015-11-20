module Prelude.Core where

open import Agda.Primitive public
  using (Level)
  renaming (lzero to zeroˡ ; lsuc to sucˡ ; _⊔_ to _⊔ˡ_)

-----------------------
-- Syntactic Helpers --
-----------------------

syntax the A x = x 𝑎𝑡 A
infix 2 the
the : ∀ {𝓁} (A : Set 𝓁) → A → A
the A x = x

begin_end : ∀ {𝓁} {A : Set 𝓁} → A → A
begin_end x = x

----------
-- Bool --
----------

data 𝔹 : Set where
  True : 𝔹
  False : 𝔹

{-# BUILTIN BOOL  𝔹 #-}
{-# BUILTIN TRUE  True #-}
{-# BUILTIN FALSE False #-}

infixr 2 if_then_else_
if_then_else_ : ∀ {𝓁} {A : Set 𝓁} → 𝔹 → A → A → A
if True then tb else fb = tb
if False then tb else fb = fb

-------------
-- Natural --
-------------

data ℕ : Set where
  Zero : ℕ
  Suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-------------
-- Integer --
-------------

data ℤ : Set where
  Neg : ℕ → ℤ
  Zero : ℤ
  Pos : ℕ → ℤ

----------
-- List --
----------

infixr 10 _∷_
data list {𝓁} (A : Set 𝓁) : Set 𝓁 where
  [] : list A
  _∷_ : A → list A → list A

{-# BUILTIN LIST list #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

----------
-- Void --
----------

data void : Set where

not : ∀ {𝓁} → Set 𝓁 → Set 𝓁
not A = A → void

exfalso : ∀ {𝓁} {A : Set 𝓁} → void → A
exfalso ()

----------
-- Unit --
----------

data unit : Set where tt : unit

------------
-- Option --
------------

data option {𝓁} (A : Set 𝓁) : Set 𝓁 where
  None : option A
  Some : A → option A

---------
-- Sum --
---------

infixr 5 _⨄_
data _⨄_ {𝓁₁ 𝓁₂} (A : Set 𝓁₁) (B : Set 𝓁₂) : Set (𝓁₁ ⊔ˡ 𝓁₂) where
  Inl : A → A ⨄ B
  Inr : B → A ⨄ B

-------------
-- Product --
-------------

infixr 6 _×_
infixr 3 _,_
record _×_ {𝓁₁ 𝓁₂} (A : Set 𝓁₁) (B : Set 𝓁₂) : Set (𝓁₁ ⊔ˡ 𝓁₂) where
  constructor _,_
  field
    π₁ : A
    π₂ : B
open _×_ public

swap : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} → A × B → B × A
swap (x , y) = (y , x)
  
-----------------
-- Exponential --
-----------------

[→] : ∀ {𝓁₁ 𝓁₂} (A : Set 𝓁₁) (B : Set 𝓁₂) → Set (𝓁₁ ⊔ˡ 𝓁₂)
[→] A B = A → B

infixr 4 _↔_
_↔_ : ∀ {𝓁₁ 𝓁₂} → Set 𝓁₁ → Set 𝓁₂ → Set (𝓁₁ ⊔ˡ 𝓁₂)
A ↔ B = (A → B) × (B → A)

-------------------
-- Dependent Sum -- 
-------------------

syntax Σ (λ x → e) = ∃ x 𝑠𝑡 e
infixr 2 Σ
infixr 2 ∃_,,_
record Σ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} (B : ∀ (x : A) → Set 𝓁₂) : Set (𝓁₁ ⊔ˡ 𝓁₂) where
  constructor ∃_,,_
  field
    dπ₁ : A
    dπ₂ : B dπ₁
open Σ public
 
syntax Σ: A (λ x → e) = ∃ x ⦂ A 𝑠𝑡 e
infixr 2 Σ:
Σ: : ∀ {𝓁₁ 𝓁₂} (A : Set 𝓁₁) (B : ∀ (x : A) → Set 𝓁₂) → Set (𝓁₁ ⊔ˡ 𝓁₂)
Σ: A B = ∃ x 𝑠𝑡 B x

--------------
-- Equality --
--------------

infix 3 _≡_
data _≡_ {𝓁} {A : Set 𝓁} (x : A) : A → Set 𝓁 where
  ↯ : x ≡ x

infix 3 _≢_
_≢_ : ∀ {𝓁} {A : Set 𝓁} → A → A → Set 𝓁
x ≢ y = not (x ≡ y)

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL ↯ #-}

subst : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : A → Set 𝓁₂} {x₁ x₂ : A} → x₁ ≡ x₂ → B x₂ → B x₁
subst ↯ B = B

change : ∀ {𝓁} {A B : Set 𝓁} → A ≡ B → A → B
change ↯ B = B

change-goal : ∀ {𝓁} {A B : Set 𝓁} → A ≡ B → B → A
change-goal ↯ B = B

xRx⸢≡⸣ : ∀ {𝓁} {A : Set 𝓁} {x : A} → x ≡ x
xRx⸢≡⸣ = ↯

◇⸢≡⸣ : ∀ {𝓁} {A : Set 𝓁} {x y : A} → x ≡ y → y ≡ x
◇⸢≡⸣ ↯ = ↯

infixr 9 _⌾⸢≡⸣_
_⌾⸢≡⸣_ : ∀ {𝓁} {A : Set 𝓁} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
_⌾⸢≡⸣_ ↯ ↯ = ↯

res-f-x : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} {f₁ f₂ : A → B} {x₁ x₂ : A} → f₁ ≡ f₂ → x₁ ≡ x₂ → f₁ x₁ ≡ f₂ x₂
res-f-x ↯ ↯ = ↯

res-x : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} {f : A → B} {x₁ x₂ : A} → x₁ ≡ x₂ → f x₁ ≡ f x₂
res-x = res-f-x ↯

res-f : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} {f₁ f₂ : A → B} {x : A} → f₁ ≡ f₂ → f₁ x ≡ f₂ x
res-f f₁≡f₂ = res-f-x f₁≡f₂ ↯

res2-f-xy :
  ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : Set 𝓁₁} {B : Set 𝓁₂} {C : Set 𝓁₃} {f₁ f₂ : A → B → C} {x₁ x₂ : A} {y₁ y₂ : B}
  → f₁ ≡ f₂ → x₁ ≡ x₂ → y₁ ≡ y₂ → f₁ x₁ y₁ ≡ f₂ x₂ y₂
res2-f-xy ↯ ↯ ↯ = ↯

res2-xy : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : Set 𝓁₁} {B : Set 𝓁₂} {C : Set 𝓁₃} {f : A → B → C} {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
res2-xy = res2-f-xy ↯

res2-f : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : Set 𝓁₁} {B : Set 𝓁₂} {C : Set 𝓁₃} {f₁ f₂ : A → B → C} {x : A} {y : B} → f₁ ≡ f₂ → f₁ x y ≡ f₂ x y
res2-f f₁≡f₂ = res2-f-xy f₁≡f₂ ↯ ↯

---------------
-- Functions --
---------------

id : ∀ {𝓁} {A : Set 𝓁} → A → A
id x = x

infixr 0 _$$_
_$$_ : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} → (A → B) → A → B
f $$ x = f x

infixr 0 do_
do_ : ∀ {𝓁} {A : Set 𝓁} → A → A
do_ x = x

infixr 1 _$_
_$_ : ∀  {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} → (A → B) → A → B
f $ x = f x

infixr 9 _∘_
_∘_ : ∀ {𝓁₁ 𝓁₂ ℓ₃} {A : Set 𝓁₁} {B : Set 𝓁₂} {C : Set ℓ₃} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g $ f x

_∘∘_ : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} {A : Set 𝓁₁} {B : Set 𝓁₂} {C : Set 𝓁₃} {D : Set 𝓁₄} → (C → D) → (A → B → C) → (A → B → D)
g ∘∘ f = _∘_ g ∘ f

const : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} → B → (A → B)
const x _ = x

infixr 2 _𝑜𝑛_
_𝑜𝑛_ : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : Set 𝓁₁} {B : Set 𝓁₂} {C : Set 𝓁₃} → (B → B → C) → (A → B) → (A → A → C)
(r 𝑜𝑛 f) x y = r (f x) (f y)

curry : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : Set 𝓁₁} {B : Set 𝓁₂} {C : Set 𝓁₃} → (A × B → C) → (A → B → C)
curry f x y = f (x , y)

uncurry : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : Set 𝓁₁} {B : Set 𝓁₂} {C : Set 𝓁₃} → (A → B → C) → (A × B → C)
uncurry f (x , y) = f x y

flip : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : Set 𝓁₁} {B : Set 𝓁₂} {C : Set 𝓁₃} → (A → B → C) → (B → A → C)
flip f y x = f x y

case_𝑜𝑓_ : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} → A → (A → B) → B
case x 𝑜𝑓 f = f x

------------
-- Lifted --
------------

record lifted 𝓁 {𝓁'} (A : Set 𝓁') : Set (𝓁 ⊔ˡ 𝓁') where
  constructor Lift
  field
    unlift : A
open lifted public

--------------
-- Remember --
--------------

-- Borrowed heavily from Ulf Norell

hidden : ∀ {𝓁} → Set 𝓁 → Set 𝓁
hidden A = unit → A

hide : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : A → Set 𝓁₂} (f : ∀ (x : A) → B x) (x : A) → hidden (B x)
hide f x tt = f x

reveal : ∀ {𝓁} {A : Set 𝓁} → hidden A → A
reveal x = x tt

data remember-hiding_𝑖𝑠_ {𝓁} {A : Set 𝓁} (x : A) (y : hidden A): Set 𝓁 where
  Was : x ≡ reveal y → remember-hiding x 𝑖𝑠 y

remember-hidden : ∀ {𝓁} {A : Set 𝓁} (x : hidden A) → remember-hiding reveal x 𝑖𝑠 x
remember-hidden f = Was ↯

remember : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : A → Set 𝓁₂} (f : ∀ (x : A) → B x) (x : A) → remember-hiding f x 𝑖𝑠 hide f x
remember f x = remember-hidden (hide f x)
