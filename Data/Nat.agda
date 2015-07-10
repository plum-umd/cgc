module Data.Nat where

open import Core
open import Relations
open import Classes

infixr 5 _+⸢ℕ⸣_
_+⸢ℕ⸣_ : ℕ → ℕ → ℕ
Zero +⸢ℕ⸣ n = n
Suc n₁ +⸢ℕ⸣ n₂ = Suc (n₁ +⸢ℕ⸣ n₂)

left-unit[+⸢ℕ⸣] : ∀ (x : ℕ) → 0 +⸢ℕ⸣ x ≡ x
left-unit[+⸢ℕ⸣] x = ↯

right-unit[+⸢ℕ⸣] : ∀ (x : ℕ) → x +⸢ℕ⸣ 0 ≡ x
right-unit[+⸢ℕ⸣] Zero = ↯
right-unit[+⸢ℕ⸣] (Suc x) rewrite right-unit[+⸢ℕ⸣] x = ↯

associativity[+⸢ℕ⸣] : ∀ (x y z : ℕ) → (x +⸢ℕ⸣ y) +⸢ℕ⸣ z ≡ x +⸢ℕ⸣ y +⸢ℕ⸣ z
associativity[+⸢ℕ⸣] Zero y z = ↯
associativity[+⸢ℕ⸣] (Suc x) y z rewrite associativity[+⸢ℕ⸣] x y z = ↯

instance
  Additive[ℕ] : Additive ℕ
  Additive[ℕ] = record
    { zero = Zero
    ; _+_ = _+⸢ℕ⸣_
    ; left-unit[+] = left-unit[+⸢ℕ⸣]
    ; right-unit[+] = right-unit[+⸢ℕ⸣]
    ; associativity[+] = associativity[+⸢ℕ⸣]
    }

infix 8 _≤⸢ℕ⸣_
data _≤⸢ℕ⸣_ : ℕ → ℕ → Set where
  Zero : ∀ {x} → Zero ≤⸢ℕ⸣ x
  Suc : ∀ {x y} → x ≤⸢ℕ⸣ y → Suc x ≤⸢ℕ⸣ Suc y

xRx[≡]⸢≤⸢ℕ⸣⸣ : reflexive[ _≡_ ] _≤⸢ℕ⸣_
xRx[≡]⸢≤⸢ℕ⸣⸣ {Zero} ↯ = Zero
xRx[≡]⸢≤⸢ℕ⸣⸣ {Suc x} ↯ = Suc (xRx[≡]⸢≤⸢ℕ⸣⸣ ↯)

_⌾⸢≤⸢ℕ⸣⸣_ : transitive _≤⸢ℕ⸣_
x ⌾⸢≤⸢ℕ⸣⸣ Zero = Zero
Suc x ⌾⸢≤⸢ℕ⸣⸣ Suc y = Suc (x ⌾⸢≤⸢ℕ⸣⸣ y)

⋈[≡]⸢≤⸢ℕ⸣⸣ : antisymmetric[ _≡_ ] _≤⸢ℕ⸣_
⋈[≡]⸢≤⸢ℕ⸣⸣ Zero Zero = ↯
⋈[≡]⸢≤⸢ℕ⸣⸣ (Suc x≤y) (Suc y≤x) = res-x $ ⋈[≡]⸢≤⸢ℕ⸣⸣ x≤y y≤x

_⋚⸢ℕ⸣_ : dec-total-order _≡_ _≤⸢ℕ⸣_
Zero  ⋚⸢ℕ⸣ Zero  = [~] ↯
Zero  ⋚⸢ℕ⸣ Suc y = [<] Zero (λ ())
Suc x ⋚⸢ℕ⸣ Zero  = [>] Zero (λ ())
Suc x ⋚⸢ℕ⸣ Suc y with x ⋚⸢ℕ⸣ y
... | [<] x≤y not[y≤x] = [<] (Suc x≤y) BAD
  where
    BAD : Suc y ≤⸢ℕ⸣ Suc x → void
    BAD (Suc y≤x) = not[y≤x] y≤x
... | [~] x≡y = [~] (res-x x≡y)
... | [>] x≥y not[y≥x] = [>] (Suc x≥y) BAD
  where
    BAD : Suc x ≤⸢ℕ⸣ Suc y → void
    BAD (Suc y≥x) = not[y≥x] y≥x

instance
  Reflexive[≤⸢ℕ⸣] : Reflexive _≤⸢ℕ⸣_
  Reflexive[≤⸢ℕ⸣] = record { xRx = xRx[≡]⸢≤⸢ℕ⸣⸣ ↯ }
  Reflexive[≡][≤⸢ℕ⸣] : Reflexive[ _≡_ ] _≤⸢ℕ⸣_
  Reflexive[≡][≤⸢ℕ⸣] = record { xRx[] = xRx[≡]⸢≤⸢ℕ⸣⸣ }
  Transitive[≤⸢ℕ⸣] : Transitive _≤⸢ℕ⸣_
  Transitive[≤⸢ℕ⸣] = record { _⌾_ = _⌾⸢≤⸢ℕ⸣⸣_ }
  Antisymmetric[≤⸢ℕ⸣] : Antisymmetric _≤⸢ℕ⸣_
  Antisymmetric[≤⸢ℕ⸣] = record { ⋈ = ⋈[≡]⸢≤⸢ℕ⸣⸣ }
  Antisymmetric[≡][≤⸢ℕ⸣] : Antisymmetric[ _≡_ ] _≤⸢ℕ⸣_
  Antisymmetric[≡][≤⸢ℕ⸣] = record { ⋈[] = ⋈[≡]⸢≤⸢ℕ⸣⸣ }
  TotalOrder[≤⸢ℕ⸣] : TotalOrder zeroˡ ℕ _≡_
  TotalOrder[≤⸢ℕ⸣] = record
    { _≤_ = _≤⸢ℕ⸣_
    ; Reflexive[][≤] = Reflexive[≡][≤⸢ℕ⸣]
    ; Transitive[≤] = Transitive[≤⸢ℕ⸣]
    ; Antisymmetric[][≤] = Antisymmetric[≡][≤⸢ℕ⸣]
    ; _⋚_ = _⋚⸢ℕ⸣_
    }

dec⸢≤⸢ℕ⸣⸣ : rel-dec _≤⸢ℕ⸣_
dec⸢≤⸢ℕ⸣⸣ x y with x ⋚⸢ℕ⸣ y
... | [<] x≤y _ = yes x≤y
... | [~] x≡y = yes (xRx[≡]⸢≤⸢ℕ⸣⸣ x≡y)
... | [>] _ not[x≥y] = no not[x≥y]

instance
  RelDec⸢≤⸢ℕ⸣⸣ : RelDec _≤⸢ℕ⸣_
  RelDec⸢≤⸢ℕ⸣⸣ = record { dec[] = dec⸢≤⸢ℕ⸣⸣ }

dec⸢<⸢ℕ⸣⸣ : rel-dec (_<_ {A = ℕ})
dec⸢<⸢ℕ⸣⸣ x y with x ⋚⸢ℕ⸣ y
... | [<] x≤y not[y≤x] = yes (x≤y , not[y≤x])
... | [~] x≡y = no (λ x<y → π₂ x<y (xRx[≡] (◇ x≡y)))
... | [>] x≥y not[y≤x] = no (λ x<y → π₂ x<y x≥y)

instance
  RelDec⸢<⸢ℕ⸣⸣ : RelDec (_<_ {A = ℕ})
  RelDec⸢<⸢ℕ⸣⸣ = record { dec[] = dec⸢<⸢ℕ⸣⸣ }

weaken-suc⸢≤⸢ℕ⸣⸣ : ∀ {x y : ℕ} → x ≤ y → x ≤ Suc y
weaken-suc⸢≤⸢ℕ⸣⸣ Zero = Zero
weaken-suc⸢≤⸢ℕ⸣⸣ (Suc x≤y) = Suc (weaken-suc⸢≤⸢ℕ⸣⸣ x≤y)

record ℕ≤[_] (x : ℕ) : Set where
  constructor mk-ℕ≤
  field
    n : ℕ
    n<x : n ≤ x

mk⸢ℕ≤↯⸣ : ∀ {x} n → (d : rel-decision _≤_ n x) → {{IY : is-yes d}} → ℕ≤[ x ]
mk⸢ℕ≤↯⸣ n (yes d) {{yep}} = mk-ℕ≤ n d

infix 5 _-⸢ℕ⸣_
_-⸢ℕ⸣_ : ∀ (x : ℕ) → ℕ≤[ x ] → ℕ
Zero -⸢ℕ⸣ mk-ℕ≤ .Zero Zero = Zero
Suc x -⸢ℕ⸣ mk-ℕ≤ .Zero Zero = x
Suc x -⸢ℕ⸣ mk-ℕ≤ (Suc y) (Suc y≤x) = x -⸢ℕ⸣ mk-ℕ≤ y y≤x

record ℕ⁺ : Set where
  constructor mk-ℕ⁺
  field
    n : ℕ
    n>0 : n > 0

mk⸢ℕ⁺↯⸣ : ∀ n → (d : rel-decision _<_ 0 n) {{IY : is-yes d}} → ℕ⁺
mk⸢ℕ⁺↯⸣ n (yes d) {{yep}} = mk-ℕ⁺ n d

infix 6 _/%⸢ℕ⸣_
_/%⸢ℕ⸣_ : ℕ → ℕ⁺ → ℕ × ℕ
x /%⸢ℕ⸣ mk-ℕ⁺ Zero    y>0 = exfalso (π₂ y>0 xRx)
x /%⸢ℕ⸣ mk-ℕ⁺ (Suc y) y>0 with loop x (0 , mk-ℕ≤ y (weaken-suc⸢≤⸢ℕ⸣⸣ xRx))
  where
    loop : ℕ → ℕ × ℕ≤[ Suc y ] → ℕ × ℕ≤[ Suc y ]
    loop Zero    (quotient , ir) = quotient , ir
    loop (Suc x) (quotient , mk-ℕ≤ Zero zero≤suc[y]) = loop x (Suc quotient , mk-ℕ≤ y (weaken-suc⸢≤⸢ℕ⸣⸣ xRx))
    loop (Suc x) (quotient , mk-ℕ≤ (Suc ir) (Suc ir≤y)) = loop x (quotient , mk-ℕ≤ ir (weaken-suc⸢≤⸢ℕ⸣⸣ ir≤y))
... | quotient , ir = quotient , Suc y -⸢ℕ⸣ ir

infix 6 _/⸢ℕ⸣_
_/⸢ℕ⸣_ : ℕ → ℕ⁺ → ℕ
x /⸢ℕ⸣ y = π₁ $ x /%⸢ℕ⸣ y

infix 6 _%⸢ℕ⸣_
_%⸢ℕ⸣_ : ℕ → ℕ⁺ → ℕ
x %⸢ℕ⸣ y = π₂ $ x /%⸢ℕ⸣ y
