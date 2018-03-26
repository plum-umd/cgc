module Prelude.Core where

open import Agda.Primitive public
  using (Level)
  renaming (lzero to 0ᴸ ; lsuc to ↑ᴸ ; _⊔_ to _⊔ᴸ_)

infixr 0 _$$_ do_
infixr 1 _$_ if_then_else_ case_𝑜𝑓_
syntax the A x = x 𝑎𝑡 A
infixl 4 the _𝑜𝑛_
infixr 10 ∃𝑠𝑡
infixr 10 ∃𝑠𝑡⦂
infixr 10 ∃𝑠𝑡ᴵ
infixr 10 ∃𝑠𝑡⦂ᴵ
infixr 11 _↔_
infixr 11 _⇉_
infixr 12 _∨_
infixr 13 _∧_
infix 14 _≡_
infix 14 _≢_
infixr 30 _⊚⸢≡⸣_ _∘_ _∘∘_
infixr 40 _∷_

-----------------------
-- Syntactic Helpers --
-----------------------

the : ∀ {ℓ} (A : Set ℓ) → A → A
the A x = x

begin_end : ∀ {ℓ} {A : Set ℓ} → A → A
begin_end x = x

------------------------------------
-- Predicate and Relation Helpers --
------------------------------------

predicate : ∀ {ℓ} ℓ' → Set ℓ → Set (↑ᴸ ℓ' ⊔ᴸ ℓ)
predicate ℓ' A = A → Set ℓ'

relation : ∀ {ℓ} ℓ' → Set ℓ → Set (↑ᴸ ℓ' ⊔ᴸ ℓ)
relation ℓ' A = A → A → Set ℓ'

proper : ∀ {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) → A → Set ℓ'
proper _R_ x = x R x

_⇉_ : ∀ {ℓ₁ ℓ₁' ℓ₂ ℓ₂'} {A : Set ℓ₁} {B : Set ℓ₂} (_R₁_ : relation ℓ₁' A) (_R₂_ : relation ℓ₂' B) → relation (ℓ₁ ⊔ᴸ ℓ₁' ⊔ᴸ ℓ₂') (A → B)
(_R₁_ ⇉ _R₂_) f g = ∀ {x y} → x R₁ y → f x R₂ g y

----------
-- Bool --
----------

data 𝔹 : Set where
  False : 𝔹
  True : 𝔹

{-# BUILTIN BOOL  𝔹 #-}
{-# BUILTIN FALSE False #-}
{-# BUILTIN TRUE  True #-}

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if True then tb else fb = tb
if False then tb else fb = fb

_⨹_ : 𝔹 → 𝔹 → 𝔹
False ⨹ b = b
b ⨹ False = b
True ⨹ True = True

_⨻_ : 𝔹 → 𝔹 → 𝔹
True ⨻ b = b
b ⨻ True = b
False ⨻ False = False

-------------
-- Natural --
-------------

data ℕ : Set where
  Zero : ℕ
  Succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

----------
-- List --
----------

data list {ℓ} (A : Set ℓ) : Set ℓ where
  [] : list A
  _∷_ : A → list A → list A

{-# BUILTIN LIST list #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

----------
-- Void --
----------

data void : Set where

¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → void

¬[_] : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B → Set ℓ₃) → A → B → Set ℓ₃
¬[ _R_ ] x y = ¬ (x R y)

exfalso : ∀ {ℓ} {A : Set ℓ} → void → A
exfalso ()

----------
-- Unit --
----------

data unit : Set where
  tt : unit

------------
-- Option --
------------

data option {ℓ} (A : Set ℓ) : Set ℓ where
  None : option A
  Some : A → option A

elim-option : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → B → (A → B) → option A → B
elim-option x _ None = x
elim-option _ f (Some x) = f x

default : ∀ {ℓ} {A : Set ℓ} → A → option A → A
default x = elim-option x (λ x → x)

---------
-- Sum --
---------

data _∨_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ᴸ ℓ₂) where
  Inl : A → A ∨ B
  Inr : B → A ∨ B

-------------
-- Product --
-------------

record _∧_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ᴸ ℓ₂) where
  constructor ⟨_,_⟩
  field
    π₁ : A
    π₂ : B
open _∧_ public

swap : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A ∧ B → B ∧ A
swap ⟨ x , y ⟩ = ⟨ y , x ⟩
  
-----------------
-- Implication --
-----------------

[→] : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) → Set (ℓ₁ ⊔ᴸ ℓ₂)
[→] A B = A → B

_↔_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ᴸ ℓ₂)
A ↔ B = (A → B) ∧ (B → A)

-------------------
-- Dependent Sum -- 
-------------------

syntax ∃𝑠𝑡 (λ x → e) = ∃ x 𝑠𝑡 e
record ∃𝑠𝑡 {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : ∀ (x : A) → Set ℓ₂) : Set (ℓ₁ ⊔ᴸ ℓ₂) where
  constructor ⟨∃_,_⟩
  field
    dπ₁ : A
    dπ₂ : B dπ₁
open ∃𝑠𝑡 public

syntax ∃𝑠𝑡⦂ A (λ x → e) = ∃ x ⦂ A 𝑠𝑡 e
∃𝑠𝑡⦂ : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : ∀ (x : A) → Set ℓ₂) → Set (ℓ₁ ⊔ᴸ ℓ₂)
∃𝑠𝑡⦂ A B = ∃ x 𝑠𝑡 B x

syntax ∃𝑠𝑡ᴵ (λ x → e) = ∃ᴵ x 𝑠𝑡 e
record ∃𝑠𝑡ᴵ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : ∀ (x : A) → Set ℓ₂) : Set (ℓ₁ ⊔ᴸ ℓ₂) where
  constructor ⟨∃_,_⟩
  field
    dπᴵ₁ : A
    .dπᴵ₂ : B dπᴵ₁
open ∃𝑠𝑡 public

syntax ∃𝑠𝑡⦂ᴵ A (λ x → e) = ∃ᴵ x ⦂ A 𝑠𝑡 e
∃𝑠𝑡⦂ᴵ : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : ∀ (x : A) → Set ℓ₂) → Set (ℓ₁ ⊔ᴸ ℓ₂)
∃𝑠𝑡⦂ᴵ A B = ∃ x 𝑠𝑡 B x

--------------
-- Equality --
--------------

data _≡_ {ℓ} {A : Set ℓ} (x : A) : predicate ℓ A where
  ↯ : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

≡[_] : ∀ {ℓ} (A : Set ℓ) → relation ℓ A
≡[ A ] = _≡_ {A = A}

_≢_ : ∀ {ℓ} {A : Set ℓ} → relation ℓ A
x ≢ y = ¬ (x ≡ y)

subst[_] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {x₁ x₂ : A} → x₁ ≡ x₂ → B x₂ → B x₁
subst[ B ] ↯ x = x

change : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
change ↯ B = B

change-goal : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → B → A
change-goal ↯ B = B

xRx⸢≡⸣ : ∀ {ℓ} {A : Set ℓ} {x : A} → x ≡ x
xRx⸢≡⸣ = ↯

◇⸢≡⸣ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
◇⸢≡⸣ ↯ = ↯

_⊚⸢≡⸣_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
_⊚⸢≡⸣_ ↯ ↯ = ↯

res[fx] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f₁ f₂ : A → B} {x₁ x₂ : A} → f₁ ≡ f₂ → x₁ ≡ x₂ → f₁ x₁ ≡ f₂ x₂
res[fx] ↯ ↯ = ↯

res[•x][_] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {x₁ x₂ : A} → x₁ ≡ x₂ → f x₁ ≡ f x₂
res[•x][ f ] = res[fx] ↯

res[•x] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} {x₁ x₂ : A} → x₁ ≡ x₂ → f x₁ ≡ f x₂
res[•x] = res[•x][ _ ]

res[f•][_] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (x : A) {f₁ f₂ : A → B} → f₁ ≡ f₂ → f₁ x ≡ f₂ x
res[f•][ x ] f₁≡f₂ = res[fx] f₁≡f₂ ↯

res[f•] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {x : A} {f₁ f₂ : A → B} → f₁ ≡ f₂ → f₁ x ≡ f₂ x
res[f•] = res[f•][ _ ]

res[fxy] :
  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {f₁ f₂ : A → B → C} {x₁ x₂ : A} {y₁ y₂ : B}
  → f₁ ≡ f₂ → x₁ ≡ x₂ → y₁ ≡ y₂ → f₁ x₁ y₁ ≡ f₂ x₂ y₂
res[fxy] ↯ ↯ ↯ = ↯

res[•xy][_] : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
res[•xy][ f ] = res[fxy] ↯

res[•xy] : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {f : A → B → C} {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
res[•xy] = res[•xy][ _ ]

res[f••][_,_] : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (x : A) (y : B) {f₁ f₂ : A → B → C} → f₁ ≡ f₂ → f₁ x y ≡ f₂ x y
res[f••][ x , y ] f₁≡f₂ = res[fxy] f₁≡f₂ ↯ ↯

res[•x•][_,_] : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (f : A → B → C) (y : B) {x₁ x₂ : A}  → x₁ ≡ x₂ → f x₁ y ≡ f x₂ y
res[•x•][ f , y ] x₁≡x₂ = res[•xy][ f ] x₁≡x₂ ↯

res[••y][_,_] : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (f : A → B → C) (x : A) {y₁ y₂ : B}  → y₁ ≡ y₂ → f x y₁ ≡ f x y₂
res[••y][ f , x ] y₁≡y₂ = res[•xy][ f ] ↯ y₁≡y₂

---------------
-- Functions --
---------------

id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

_$_ : ∀  {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → A → B
f $ x = f x

do_ : ∀ {ℓ} {A : Set ℓ} → A → A
do_ x = x

_$$_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → A → B
f $$ x = f x

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g $ f x

_∘∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ₄} → (C → D) → (A → B → C) → (A → B → D)
g ∘∘ f = _∘_ g ∘ f

const : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → B → (A → B)
const x _ = x

_𝑜𝑛_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (B → B → C) → (A → B) → (A → A → C)
(r 𝑜𝑛 f) x y = r (f x) (f y)

curry : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (A ∧ B → C) → (A → B → C)
curry f x y = f ⟨ x , y ⟩

uncurry : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (A → B → C) → (A ∧ B → C)
uncurry f ⟨ x , y ⟩ = f x y

flip : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (A → B → C) → (B → A → C)
flip f y x = f x y

case_𝑜𝑓_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A → (A → B) → B
case x 𝑜𝑓 f = f x

--------------
-- Remember --
--------------

-- Borrowed heavily from Ulf Norell

hidden : ∀ {ℓ} → Set ℓ → Set ℓ
hidden A = unit → A

hide : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} (f : ∀ (x : A) → B x) (x : A) → hidden (B x)
hide f x tt = f x

reveal : ∀ {ℓ} {A : Set ℓ} → hidden A → A
reveal x = x tt

data recall_𝑖𝑠_ {ℓ} {A : Set ℓ} (x : A) (y : hidden A) : Set ℓ where
  Was : x ≡ reveal y → recall x 𝑖𝑠 y

remember/Π : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} (f : ∀ (x : A) → B x) (x : A) → recall f x 𝑖𝑠 hide f x
remember/Π f x = Was ↯

remember : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (x : A) → recall f x 𝑖𝑠 hide f x
remember = remember/Π
