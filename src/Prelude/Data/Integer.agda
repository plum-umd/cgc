module Prelude.Data.Integer where

open import Prelude.Core
open import Prelude.Relations
open import Prelude.Classes

open import Prelude.Data.Natural

----------------
-- Conversion --
----------------

record ToInteger {𝓁} (A : Set 𝓁) : Set 𝓁 where
  constructor mk[ToInteger]
  field
    𝕫 : A → ℤ
open ToInteger {{...}} public

𝕫ⁿ : ℕ → ℤ
𝕫ⁿ Zero = Zero
𝕫ⁿ (Suc n) = Pos n

instance
  ToInteger[ℕ] : ToInteger ℕ
  ToInteger[ℕ] = mk[ToInteger] 𝕫ⁿ

-------------------
-- ≤ and < Order --
-------------------

infix 8 _≤ᶻ_
data _≤ᶻ_ : ℤ → ℤ → Set where
  Neg≤Neg   : ∀ {n₁ n₂} → n₂ ≤ n₁ → Neg n₁ ≤ᶻ Neg n₂
  Neg≤Zero  : ∀ {n₁}    → Neg n₁ ≤ᶻ Zero
  Neg≤Pos   : ∀ {n₁ n₂} → Neg n₁ ≤ᶻ Pos n₂
  Zero≤Zero :             Zero ≤ᶻ Zero
  Zero≤Pos  : ∀ {n₂}    → Zero ≤ᶻ Pos n₂
  Pos≤Pos   : ∀ {n₁ n₂} → n₁ ≤ n₂ → Pos n₁ ≤ᶻ Pos n₂

data _<ᶻ_ : ℤ → ℤ → Set where
  Neg<Neg : ∀ {n₁ n₂} → n₂ <ⁿ n₁ → Neg n₁ <ᶻ Neg n₂
  Neg<Zero : ∀ {n₁} → Neg n₁ <ᶻ Zero
  Neg<Pos : ∀ {n₁ n₂} → Neg n₁ <ᶻ Pos n₂
  Zero<Pos : ∀ {n₂} → Zero <ᶻ Pos n₂
  Pos<Pos : ∀ {n₁ n₂} → n₁ < n₂ → Pos n₁ <ᶻ Pos n₂

xRx⸢≤ᶻ⸣ : reflexive _≤ᶻ_
xRx⸢≤ᶻ⸣ {Neg n} = Neg≤Neg xRx
xRx⸢≤ᶻ⸣ {Zero} = Zero≤Zero
xRx⸢≤ᶻ⸣ {Pos n} = Pos≤Pos xRx

infixr 9 _⌾⸢≤ᶻ⸣_
_⌾⸢≤ᶻ⸣_ : transitive _≤ᶻ_
Neg≤Neg g ⌾⸢≤ᶻ⸣ Neg≤Neg f = Neg≤Neg (f ⌾ g)
Neg≤Zero  ⌾⸢≤ᶻ⸣ Neg≤Neg f = Neg≤Zero
Neg≤Pos   ⌾⸢≤ᶻ⸣ Neg≤Neg f = Neg≤Pos
Zero≤Zero ⌾⸢≤ᶻ⸣ Neg≤Zero  = Neg≤Zero
Zero≤Zero ⌾⸢≤ᶻ⸣ Zero≤Zero = Zero≤Zero
Zero≤Pos  ⌾⸢≤ᶻ⸣ Neg≤Zero  = Neg≤Pos
Zero≤Pos  ⌾⸢≤ᶻ⸣ Zero≤Zero = Zero≤Pos
Pos≤Pos g ⌾⸢≤ᶻ⸣ Neg≤Pos   = Neg≤Pos
Pos≤Pos g ⌾⸢≤ᶻ⸣ Zero≤Pos  = Zero≤Pos
Pos≤Pos g ⌾⸢≤ᶻ⸣ Pos≤Pos f = Pos≤Pos (g ⌾ f)

⋈⸢≤ᶻ⸣ : antisymmetric[ _≡_ ] _≤ᶻ_
⋈⸢≤ᶻ⸣ (Neg≤Neg f) (Neg≤Neg g) = res-x (⋈ g f)
⋈⸢≤ᶻ⸣ Neg≤Zero ()
⋈⸢≤ᶻ⸣ Neg≤Pos ()
⋈⸢≤ᶻ⸣ Zero≤Zero Zero≤Zero = ↯
⋈⸢≤ᶻ⸣ Zero≤Pos ()
⋈⸢≤ᶻ⸣ (Pos≤Pos f) (Pos≤Pos g) = res-x (⋈ f g)

_⋚ᶻ_ : dec-total-order _≡_ _≤ᶻ_
Neg n₁ ⋚ᶻ Neg n₂ with n₁ ⋚ n₂
... | [<] n₁≤n₂ n₂≤/n₁ = [>] (Neg≤Neg n₁≤n₂) (λ{ (Neg≤Neg n₁≤n₂) → n₂≤/n₁ n₁≤n₂ })
... | [~] n₁≡n₂ rewrite n₁≡n₂ = [~] ↯
... | [>] n₂≤n₁ n₁≤/n₂ = [<] (Neg≤Neg n₂≤n₁) (λ{ (Neg≤Neg n₂≤n₁) → n₁≤/n₂ n₂≤n₁ })
Neg n₁ ⋚ᶻ Zero = [<] Neg≤Zero (λ ())
Neg n₁ ⋚ᶻ Pos n₂ = [<] Neg≤Pos (λ ())
Zero ⋚ᶻ Neg n₂ = [>] Neg≤Zero (λ ())
Zero ⋚ᶻ Zero = [~] ↯
Zero ⋚ᶻ Pos n₂ = [<] Zero≤Pos (λ ())
Pos n₁ ⋚ᶻ Neg n₂ = [>] Neg≤Pos (λ ())
Pos n₁ ⋚ᶻ Zero = [>] Zero≤Pos (λ ())
Pos n₁ ⋚ᶻ Pos n₂ with n₁ ⋚ n₂
... | [<] n₁≤n₂ n₂≤/n₁ = [<] (Pos≤Pos n₁≤n₂) (λ{ (Pos≤Pos n₁≤n₂) → n₂≤/n₁ n₁≤n₂ })
... | [~] n₁≡n₂ rewrite n₁≡n₂ = [~] ↯
... | [>] n₂≤n₁ n₁≤/n₂ = [>] (Pos≤Pos n₂≤n₁) (λ{ (Pos≤Pos n₂≤n₁) → n₁≤/n₂ n₂≤n₁ })

correct[<ᶻ] : ∀ {i j} → i <ᶻ j ↔ i ≤ᶻ j × not (j ≤ᶻ i)
correct[<ᶻ] = LHS , RHS
  where
    LHS : ∀ {i j} → i <ᶻ j → i ≤ᶻ j × not (j ≤ᶻ i)
    LHS (Neg<Neg n₂<n₁) = Neg≤Neg (π₁ (π₁ correct[<ⁿ] n₂<n₁)) , λ{ (Neg≤Neg n₂≤n₁) → π₂ (π₁ correct[<ⁿ] n₂<n₁) n₂≤n₁ }
    LHS Neg<Zero = Neg≤Zero , λ ()
    LHS Neg<Pos = Neg≤Pos , λ ()
    LHS Zero<Pos = Zero≤Pos , λ ()
    LHS (Pos<Pos n₁<n₂) = Pos≤Pos (π₁ (π₁ correct[<ⁿ] n₁<n₂)) , (λ{ (Pos≤Pos n₁≤n₂)  → π₂ (π₁ correct[<ⁿ] n₁<n₂) n₁≤n₂ })
    RHS : ∀ {i j} → i ≤ᶻ j × not (j ≤ᶻ i) → i <ᶻ j
    RHS (Neg≤Neg n₂≤n₁ , ¬j≤i) = Neg<Neg (π₂ correct[<ⁿ] (n₂≤n₁ , λ n₁≤n₂ → ¬j≤i (Neg≤Neg n₁≤n₂)))
    RHS (Neg≤Zero , ¬j≤i) = Neg<Zero
    RHS (Neg≤Pos , ¬j≤i) = Neg<Pos
    RHS (Zero≤Zero , ¬j≤i) = exfalso (¬j≤i Zero≤Zero)
    RHS (Zero≤Pos , ¬j≤i) = Zero<Pos
    RHS (Pos≤Pos n₁≤n₂ , ¬j≤i) = Pos<Pos (π₂ correct[<ⁿ] (n₁≤n₂ , (λ n₂≤n₁ → ¬j≤i (Pos≤Pos n₂≤n₁))))

instance
  Reflexive[≤ᶻ] : Reflexive _≤ᶻ_
  Reflexive[≤ᶻ] = record { xRx = xRx⸢≤ᶻ⸣ }
  Transitive[≤ᶻ] : Transitive _≤ᶻ_
  Transitive[≤ᶻ] = record { _⌾_ = _⌾⸢≤ᶻ⸣_ }
  Antisymmetric[≤ᶻ] : Antisymmetric _≤ᶻ_
  Antisymmetric[≤ᶻ] = record { ⋈ = ⋈⸢≤ᶻ⸣ }
  TotalOrder[≤ᶻ] : TotalOrder zeroˡ ℤ
  TotalOrder[≤ᶻ] = record
    { _≤_ = _≤ᶻ_
    ; _<_ = _<ᶻ_
    ; correct[<] = correct[<ᶻ]
    ; Reflexive[≤] = Reflexive[≤ᶻ]
    ; Transitive[≤] = Transitive[≤ᶻ]
    ; Antisymmetric[≤] = Antisymmetric[≤ᶻ]
    ; _⋚_ = _⋚ᶻ_
    }

------------------
-- ≡ᶻ Decidable --
------------------

dec[≡ᶻ] : dec-rel (_≡_ {A = ℤ})
dec[≡ᶻ] i₁ i₂ with i₁ ⋚ᶻ i₂
... | [<] i₁≤i₂ i₂≤/i₁ = No (λ i₁≡i₂ → i₂≤/i₁ (xRx[≡] (◇ i₁≡i₂)))
... | [~] i₁≡i₂ = Yes i₁≡i₂
... | [>] i₂≤i₁ i₁≤/i₂ = No (λ i₁≡i₂ → i₁≤/i₂ (xRx[≡] i₁≡i₂))

instance
  DecRel[≡ᶻ] : DecRel (_≡_ {A = ℤ})
  DecRel[≡ᶻ] = record { dec[] = dec[≡ᶻ] }
  
-------------
-- Bounded --
-------------

record ℤ⁺ : Set zeroˡ where
  constructor mk[ℤ⁺]
  field
    i : ℤ
    i≠0 : i ≢ Zero
   
mk[ℤ⁺]⸢↯⸣ : ∀ (i : ℤ) → {{IY : not-rel (dec[ _≡_ ] i Zero)}} → ℤ⁺
mk[ℤ⁺]⸢↯⸣ i {{IR}} with dec[ _≡_ ] i Zero
mk[ℤ⁺]⸢↯⸣ i {{↯Rel}} | No i≠0 = mk[ℤ⁺] i i≠0

-----------
-- Signs --
-----------

data signᶻ : Set where Zero [-] [+] : signᶻ

‖_‖ : ℤ → ℕ
‖ Neg n ‖ = Suc n
‖ Zero  ‖ = Zero
‖ Pos n ‖ = Suc n

signofᶻ : ℤ → signᶻ
signofᶻ (Neg _) = [-]
signofᶻ Zero = Zero
signofᶻ (Pos _) = [+]

correct[‖‖] : ∀ n → ‖ 𝕫 n ‖ ≡ n
correct[‖‖] Zero = ↯
correct[‖‖] (Suc n) = ↯

⁻ᶻ_ : ℤ → ℤ
⁻ᶻ Neg n = Pos n
⁻ᶻ Zero = Zero
⁻ᶻ Pos n = Neg n

-------------------------------
-- Successor and Predecessor --
-------------------------------

sucᶻ : ℤ → ℤ
sucᶻ (Neg Zero) = Zero
sucᶻ (Neg (Suc n)) = Neg n
sucᶻ Zero = Pos Zero
sucᶻ (Pos n) = Pos (Suc n)

predᶻ : ℤ → ℤ
predᶻ (Neg n) = Neg (Suc n)
predᶻ Zero = Neg Zero
predᶻ (Pos Zero) = Zero
predᶻ (Pos (Suc n)) = Pos n

pred[suc[i]]=i : ∀ i → predᶻ (sucᶻ i) ≡ i
pred[suc[i]]=i (Neg Zero) = ↯
pred[suc[i]]=i (Neg (Suc n)) = ↯
pred[suc[i]]=i Zero = ↯
pred[suc[i]]=i (Pos Zero) = ↯
pred[suc[i]]=i (Pos (Suc n)) = ↯

suc[pred[i]]=i : ∀ i → sucᶻ (predᶻ i) ≡ i
suc[pred[i]]=i (Neg Zero) = ↯
suc[pred[i]]=i (Neg (Suc n)) = ↯
suc[pred[i]]=i Zero = ↯
suc[pred[i]]=i (Pos Zero) = ↯
suc[pred[i]]=i (Pos (Suc n)) = ↯

--------------
-- Addition --
--------------

infixr 5 _+ᶻ_
_+ᶻ_ : ℤ → ℤ → ℤ
Neg Zero     +ᶻ n₂ = predᶻ n₂
Neg (Suc n₁) +ᶻ n₂ = predᶻ (Neg n₁ +ᶻ n₂)
Zero         +ᶻ n₂ = n₂
Pos Zero     +ᶻ n₂ = sucᶻ n₂
Pos (Suc n₁) +ᶻ n₂ = sucᶻ (Pos n₁ +ᶻ n₂)

left-unit[+ᶻ] : ∀ i → Zero +ᶻ i ≡ i
left-unit[+ᶻ] i = ↯

right-unit[+ᶻ] : ∀ i → i +ᶻ Zero ≡ i
right-unit[+ᶻ] (Neg Zero) = ↯
right-unit[+ᶻ] (Neg (Suc n)) rewrite right-unit[+ᶻ] (Neg n) = ↯
right-unit[+ᶻ] Zero = ↯
right-unit[+ᶻ] (Pos Zero) = ↯
right-unit[+ᶻ] (Pos (Suc n)) rewrite right-unit[+ᶻ] (Pos n) = ↯

pred[i+j]=pred[i]+j : ∀ i j → predᶻ (i +ᶻ j) ≡ predᶻ i +ᶻ j
pred[i+j]=pred[i]+j (Neg n) j = ↯
pred[i+j]=pred[i]+j Zero j = ↯
pred[i+j]=pred[i]+j (Pos Zero) j rewrite pred[suc[i]]=i j = ↯
pred[i+j]=pred[i]+j (Pos (Suc n)) j rewrite pred[suc[i]]=i (Pos n +ᶻ j) = ↯

suc[i+j]=suc[i]+j : ∀ i j → sucᶻ (i +ᶻ j) ≡ sucᶻ i +ᶻ j
suc[i+j]=suc[i]+j (Neg Zero) j rewrite suc[pred[i]]=i j = ↯
suc[i+j]=suc[i]+j (Neg (Suc n)) j rewrite suc[pred[i]]=i (Neg n +ᶻ j) = ↯
suc[i+j]=suc[i]+j Zero j = ↯
suc[i+j]=suc[i]+j (Pos n) j = ↯

associative[+ᶻ] : ∀ i j k → (i +ᶻ j) +ᶻ k ≡ i +ᶻ (j +ᶻ k)
associative[+ᶻ] (Neg Zero) j k rewrite pred[i+j]=pred[i]+j j k = ↯
associative[+ᶻ] (Neg (Suc n)) j k rewrite ◇ $ associative[+ᶻ] (Neg n) j k | pred[i+j]=pred[i]+j (Neg n +ᶻ j) k = ↯
associative[+ᶻ] Zero j k = ↯
associative[+ᶻ] (Pos Zero) j k rewrite suc[i+j]=suc[i]+j j k = ↯
associative[+ᶻ] (Pos (Suc n)) j k rewrite ◇ $ associative[+ᶻ] (Pos n) j k | suc[i+j]=suc[i]+j (Pos n +ᶻ j) k = ↯

postulate
  commutative[+ᶻ] : ∀ i j → i +ᶻ j ≡ j +ᶻ i
-- commutative[+ᶻ] (Neg Zero) (Neg Zero) = ↯
-- commutative[+ᶻ] (Neg (Suc n)) j rewrite commutative[+ᶻ] (Neg n) j = {!!}
-- commutative[+ᶻ] i (Neg (Suc n)) rewrite ◇ $ commutative[+ᶻ] i (Neg n) = {!!}
-- commutative[+ᶻ] Zero j = {!!}
-- commutative[+ᶻ] i Zero = {!!}
-- commutative[+ᶻ] (Pos n) j = {!!}
-- commutative[+ᶻ] i (Pos n) = {!!}

instance
  Additive[ℤ] : Additive ℤ
  Additive[ℤ] = record
    { zero = 𝕫 0
    ; _+_ = _+ᶻ_
    ; left-unit[+] = left-unit[+ᶻ]
    ; right-unit[+] = right-unit[+ᶻ]
    ; associative[+] = associative[+ᶻ]
    ; commutative[+] = commutative[+ᶻ]
    }

-----------------
-- Subtraction --
-----------------

infix 5 _-ᶻ_
_-ᶻ_ : ℤ → ℤ → ℤ
i₁ -ᶻ i₂ = i₁ +ᶻ ⁻ᶻ i₂

postulate
  correct[-ᶻ] : ∀ i j → j +ᶻ (i -ᶻ j) ≡ i

instance
  Subtractive[ℤ] : Subtractive ℤ
  Subtractive[ℤ] = record
    { _-_ = _-ᶻ_
    ; correct[-] = correct[-ᶻ]
    }

--------------------
-- Multiplication --
--------------------

infixr 6 _⨯ᶻ_
_⨯ᶻ_ : ℤ → ℤ → ℤ
Neg Zero ⨯ᶻ i₂ = ⁻ᶻ i₂
Neg (Suc n₁) ⨯ᶻ i₂ = ⁻ᶻ i₂ +ᶻ (Neg n₁ ⨯ᶻ i₂)
Zero ⨯ᶻ i₂ = Zero
Pos Zero ⨯ᶻ i₂ = i₂
Pos (Suc n₁) ⨯ᶻ i₂ = i₂ +ᶻ (Pos n₁ ⨯ᶻ i₂)

postulate
  left-zero[⨯ᶻ] : ∀ i → 𝕫 0 ⨯ᶻ i ≡ 𝕫 0
  right-zero[⨯ᶻ] : ∀ i → i ⨯ᶻ 𝕫 0 ≡ 𝕫 0
  left-unit[⨯ᶻ] : ∀ i → 𝕫 1 ⨯ᶻ i ≡ i
  right-unit[⨯ᶻ] : ∀ i → i ⨯ᶻ 𝕫 1 ≡ i
  distributive[⨯ᶻ] : ∀ i j k → (i +ᶻ j) ⨯ᶻ k ≡ i ⨯ᶻ k +ᶻ j ⨯ᶻ k
  associative[⨯ᶻ] : ∀ i j k → (i ⨯ᶻ j) ⨯ᶻ k ≡ i ⨯ᶻ (j ⨯ᶻ k)
  commutative[⨯ᶻ] : ∀ i j → i ⨯ᶻ j ≡ j ⨯ᶻ i

instance
  Multiplicative[ℤ] : Multiplicative ℤ
  Multiplicative[ℤ] = record
    { one = 𝕫 1
    ; _⨯_ = _⨯ᶻ_
    ; left-zero[⨯] = left-zero[⨯ᶻ]
    ; right-zero[⨯] = right-zero[⨯ᶻ]
    ; left-unit[⨯] = left-unit[⨯ᶻ]
    ; right-unit[⨯] = right-unit[⨯ᶻ]
    ; associative[⨯] = associative[⨯ᶻ]
    ; commutative[⨯] = commutative[⨯ᶻ]
    ; distributive[⨯] = distributive[⨯ᶻ]
    }

--------------
-- Division --
--------------

infix 6 _/%ᶻ_‖_
_/%ᶻ_‖_ : ∀ (i j : ℤ) → j ≢ 𝕫 0 → ℤ × ℤ
Zero /%ᶻ j ‖ p = Zero , Zero
i /%ᶻ Zero ‖ p = exfalso $ p ↯
Neg n /%ᶻ Neg m ‖ p with Suc n /%ⁿ Suc m ‖ Suc Zero
... | quotient , remainder = 𝕫 quotient , ⁻ᶻ 𝕫 remainder
Neg n /%ᶻ Pos m ‖ p with Suc n /%ⁿ Suc m ‖ Suc Zero
... | quotient , remainder = ⁻ᶻ 𝕫 quotient , ⁻ᶻ 𝕫 remainder
Pos n /%ᶻ Neg m ‖ p with Suc n /%ⁿ Suc m ‖ Suc Zero
... | quotient , remainder = ⁻ᶻ 𝕫 quotient , 𝕫 remainder
Pos n /%ᶻ Pos m ‖ p with Suc n /%ⁿ Suc m ‖ Suc Zero
... | quotient , remainder = 𝕫 quotient , 𝕫 remainder

test-%/ᶻ-1 : (𝕫 8 /%ᶻ 𝕫 6 ‖ ↯not-rel) ≡ (𝕫ⁿ 1 , 𝕫ⁿ 2)
test-%/ᶻ-1 = ↯

test-%/ᶻ-2 : (⁻ᶻ 𝕫 8 /%ᶻ 𝕫 6 ‖ ↯not-rel) ≡ (⁻ᶻ 𝕫ⁿ 1 , ⁻ᶻ 𝕫ⁿ 2)
test-%/ᶻ-2 = ↯

test-%/ᶻ-3 : (𝕫 8 /%ᶻ ⁻ᶻ 𝕫 6 ‖ ↯not-rel) ≡ (⁻ᶻ 𝕫ⁿ 1 , 𝕫ⁿ 2)
test-%/ᶻ-3 = ↯

test-%/ᶻ-4 : (⁻ᶻ 𝕫 8 /%ᶻ ⁻ᶻ 𝕫 6 ‖ ↯not-rel) ≡ (𝕫ⁿ 1 , ⁻ᶻ 𝕫ⁿ 2)
test-%/ᶻ-4 = ↯

postulate
  correct[/%‖ᶻ] : ∀ i j (j≢0 : j ≢ 𝕫 0) → let quo , rem = i /%ᶻ j ‖ j≢0 in j ⨯ᶻ quo +ᶻ rem ≡ i

instance
  DivMod[ℤ] : DivModᵖ ℤ (λ i j → j ≢ 𝕫 0)
  DivMod[ℤ] = record
    { _/%_‖_ = _/%ᶻ_‖_
    ; correct[/%‖] = correct[/%‖ᶻ]
    }
