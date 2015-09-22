module Data.Integer where

open import Core
open import Relations
open import Classes

open import Data.Nat

data ℤ : Set where
  Pos : ℕ → ℤ
  Zero : ℤ
  Neg : ℕ → ℤ

infix 8 _≤⸢ℤ⸣_
data _≤⸢ℤ⸣_ : ℤ → ℤ → Set where
  Pos      : ∀ {x y} → x ≤ y → Pos x ≤⸢ℤ⸣ Pos y
  Zero     :           Zero ≤⸢ℤ⸣ Zero
  Zero≤Pos : ∀ {y}   → Zero ≤⸢ℤ⸣ Pos y
  Neg      : ∀ {x y} → x ≥ y → Neg x ≤⸢ℤ⸣ Neg y
  Neg≤Zero : ∀ {x}   → Neg x ≤⸢ℤ⸣ Zero
  Neg≤Pos  : ∀ {x y} → Neg x ≤⸢ℤ⸣ Pos y

xRx⸢≤⸢ℤ⸣⸣[≡] : reflexive[ _≡_ ] _≤⸢ℤ⸣_
xRx⸢≤⸢ℤ⸣⸣[≡] {Pos x} ↯ = Pos xRx
xRx⸢≤⸢ℤ⸣⸣[≡] {Zero}  ↯ = Zero
xRx⸢≤⸢ℤ⸣⸣[≡] {Neg x} ↯ = Neg xRx

infixr 9 _⌾⸢≤⸢ℤ⸣⸣_
_⌾⸢≤⸢ℤ⸣⸣_ : transitive _≤⸢ℤ⸣_
Pos g    ⌾⸢≤⸢ℤ⸣⸣ Pos f    = Pos (g ⌾ f)
Pos g    ⌾⸢≤⸢ℤ⸣⸣ Zero≤Pos = Zero≤Pos
Pos g    ⌾⸢≤⸢ℤ⸣⸣ Neg≤Pos  = Neg≤Pos
Zero     ⌾⸢≤⸢ℤ⸣⸣ Zero     = Zero
Zero     ⌾⸢≤⸢ℤ⸣⸣ Neg≤Zero = Neg≤Zero
Zero≤Pos ⌾⸢≤⸢ℤ⸣⸣ Zero     = Zero≤Pos
Zero≤Pos ⌾⸢≤⸢ℤ⸣⸣ Neg≤Zero = Neg≤Pos
Neg g    ⌾⸢≤⸢ℤ⸣⸣ Neg f    = Neg (f ⌾ g)
Neg≤Zero ⌾⸢≤⸢ℤ⸣⸣ Neg f    = Neg≤Zero
Neg≤Pos  ⌾⸢≤⸢ℤ⸣⸣ Neg f    = Neg≤Pos

⋈⸢≤⸢ℤ⸣⸣ : antisymmetric[ _≡_ ] _≤⸢ℤ⸣_
⋈⸢≤⸢ℤ⸣⸣ (Pos f) (Pos g) = res-x (⋈ f g)
⋈⸢≤⸢ℤ⸣⸣ Zero Zero = ↯
⋈⸢≤⸢ℤ⸣⸣ Zero≤Pos ()
⋈⸢≤⸢ℤ⸣⸣ (Neg f) (Neg g) = res-x (⋈ g f)
⋈⸢≤⸢ℤ⸣⸣ Neg≤Zero ()
⋈⸢≤⸢ℤ⸣⸣ Neg≤Pos ()

data sign⸢ℤ⸣ : Set where Zero [+] [-] : sign⸢ℤ⸣

‖_‖ : ℤ → ℕ
‖ Pos x ‖ = Suc x
‖ Zero  ‖ = Zero
‖ Neg x ‖ = Suc x

signage⸢ℤ⸣ : ℤ → sign⸢ℤ⸣
signage⸢ℤ⸣ (Pos _) = [+]
signage⸢ℤ⸣ Zero = Zero
signage⸢ℤ⸣ (Neg _) = [-]

ℕ-to-ℤ : ℕ → ℤ
ℕ-to-ℤ Zero = Zero
ℕ-to-ℤ (Suc n) = Pos n

ℕ-to-ℤ-≡ : ∀ {n} → ‖ ℕ-to-ℤ n ‖ ≡ n
ℕ-to-ℤ-≡ {Zero} = ↯
ℕ-to-ℤ-≡ {Suc n} = ↯

suc⸢ℤ⸣ : ℤ → ℤ
suc⸢ℤ⸣ (Pos x) = Pos (Suc x)
suc⸢ℤ⸣ Zero = Pos Zero
suc⸢ℤ⸣ (Neg Zero) = Zero
suc⸢ℤ⸣ (Neg (Suc x)) = Neg x

pred⸢ℤ⸣ : ℤ → ℤ
pred⸢ℤ⸣ (Pos Zero) = Zero
pred⸢ℤ⸣ (Pos (Suc x)) = Pos x
pred⸢ℤ⸣ Zero = Neg Zero
pred⸢ℤ⸣ (Neg x) = Neg (Suc x)

infixr 5 _+⸢ℤ⸣_
_+⸢ℤ⸣_ : ℤ → ℤ → ℤ
Pos Zero    +⸢ℤ⸣ y = suc⸢ℤ⸣ y
Pos (Suc x) +⸢ℤ⸣ y = suc⸢ℤ⸣ (Pos x +⸢ℤ⸣ y)
Zero        +⸢ℤ⸣ y = y
Neg Zero    +⸢ℤ⸣ y = pred⸢ℤ⸣ y
Neg (Suc x) +⸢ℤ⸣ y = pred⸢ℤ⸣ (Neg x +⸢ℤ⸣ y)

neg⸢ℤ⸣ : ℤ → ℤ
neg⸢ℤ⸣ (Pos x) = Neg x
neg⸢ℤ⸣ Zero = Zero
neg⸢ℤ⸣ (Neg x) = Pos x

infix 5 _-⸢ℤ⸣_
_-⸢ℤ⸣_ : ℤ → ℤ → ℤ
x -⸢ℤ⸣ y = x +⸢ℤ⸣ neg⸢ℤ⸣ y

infixr 6 _*⸢ℤ⸣_
_*⸢ℤ⸣_ : ℤ → ℤ → ℤ
Pos Zero *⸢ℤ⸣ y = y
Pos (Suc x) *⸢ℤ⸣ y = y +⸢ℤ⸣ (Pos x *⸢ℤ⸣ y)
Zero *⸢ℤ⸣ y = Zero
Neg Zero *⸢ℤ⸣ y = neg⸢ℤ⸣ y
Neg (Suc x) *⸢ℤ⸣ y = y -⸢ℤ⸣ (Neg x *⸢ℤ⸣ y)

record ℤ⁺ : Set zeroˡ where
  constructor mk-ℤ⁺
  field
    n : ℤ
    n≠0 : n ≢ Zero
   
mk⸢ℤ⁺↯⸣ : ∀ n → (d : rel-decision _≢_ n Zero) {{IY : is-yes d}} → ℤ⁺
mk⸢ℤ⁺↯⸣ n (Yes d) {{Yep}} = mk-ℤ⁺ n d

infix 6 _/%⸢ℤ⸣_
_/%⸢ℤ⸣_ : ℤ → ℤ⁺ → ℤ × ℤ
Pos x /%⸢ℤ⸣ mk-ℤ⁺ (Pos y) y≠0 with Suc x /%⸢ℕ⸣ mk-ℕ⁺ (Suc y) (Zero , (λ ()))
... | quotient , remainder = ℕ-to-ℤ quotient , ℕ-to-ℤ remainder
Pos x /%⸢ℤ⸣ mk-ℤ⁺ Zero    y≠0 = exfalso (y≠0 ↯)
Pos x /%⸢ℤ⸣ mk-ℤ⁺ (Neg y) y≠0 with Suc x /%⸢ℕ⸣ mk-ℕ⁺ (Suc y) (Zero , (λ ()))
... | quotient , remainder = neg⸢ℤ⸣ (ℕ-to-ℤ quotient) , ℕ-to-ℤ remainder
Zero  /%⸢ℤ⸣ y                = Zero , Zero
Neg x /%⸢ℤ⸣ mk-ℤ⁺ (Pos y) y≠0 with Suc x /%⸢ℕ⸣ mk-ℕ⁺ (Suc y) (Zero , (λ ()))
... | quotient , remainder = neg⸢ℤ⸣ (ℕ-to-ℤ quotient) , neg⸢ℤ⸣ (ℕ-to-ℤ remainder)
Neg x /%⸢ℤ⸣ mk-ℤ⁺ Zero    y≠0 = exfalso (y≠0 ↯)
Neg x /%⸢ℤ⸣ mk-ℤ⁺ (Neg y) y≠0 with Suc x /%⸢ℕ⸣ mk-ℕ⁺ (Suc y) (Zero , (λ ()))
... | quotient , remainder = ℕ-to-ℤ quotient , ℕ-to-ℤ remainder

infix 6 _/⸢ℤ⸣_
_/⸢ℤ⸣_ : ℤ → ℤ⁺ → ℤ
x /⸢ℤ⸣ y = π₁ (x /%⸢ℤ⸣ y)

_%⸢ℤ⸣_ : ℤ → ℤ⁺ → ℤ
x %⸢ℤ⸣ y = π₂ (x /%⸢ℤ⸣ y)
