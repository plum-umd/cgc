module Prelude.Data.Integer where

open import Prelude.Core
open import Prelude.Classes
open import Prelude.Orders

open import Prelude.Data.Natural

-------------
-- Integer --
-------------

data ℤ : Set where
  Neg : ℕ → ℤ
  Zero : ℤ
  Pos : ℕ → ℤ

----------------
-- Conversion --
----------------

record ToInteger {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mk[ToInteger]
  field
    𝕫 : A → ℤ
open ToInteger {{…}} public

𝕫ⁿ : ℕ → ℤ
𝕫ⁿ Zero = Zero
𝕫ⁿ (Succ n) = Pos n

instance
  ToInteger[ℕ] : ToInteger ℕ
  ToInteger[ℕ] = mk[ToInteger] 𝕫ⁿ

-------------------
-- ≤ and < Order --
-------------------

data _≤ᶻ_ : ℤ → ℤ → Set where
  Neg≤Neg   : ∀ {n₁ n₂} → n₂ ≤ n₁ → Neg n₁ ≤ᶻ Neg n₂
  Neg≤Zero  : ∀ {n₁}    → Neg n₁ ≤ᶻ Zero
  Neg≤Pos   : ∀ {n₁ n₂} → Neg n₁ ≤ᶻ Pos n₂
  Zero≤Zero :             Zero ≤ᶻ Zero
  Zero≤Pos  : ∀ {n₂}    → Zero ≤ᶻ Pos n₂
  Pos≤Pos   : ∀ {n₁ n₂} → n₁ ≤ n₂ → Pos n₁ ≤ᶻ Pos n₂

xRx⸢≤ᶻ⸣ : reflexive _≤ᶻ_
xRx⸢≤ᶻ⸣ {Neg n} = Neg≤Neg xRx
xRx⸢≤ᶻ⸣ {Zero} = Zero≤Zero
xRx⸢≤ᶻ⸣ {Pos n} = Pos≤Pos xRx

_⊚⸢≤ᶻ⸣_ : transitive _≤ᶻ_
Neg≤Neg g ⊚⸢≤ᶻ⸣ Neg≤Neg f = Neg≤Neg (f ⊚ g)
Neg≤Zero  ⊚⸢≤ᶻ⸣ Neg≤Neg f = Neg≤Zero
Neg≤Pos   ⊚⸢≤ᶻ⸣ Neg≤Neg f = Neg≤Pos
Zero≤Zero ⊚⸢≤ᶻ⸣ Neg≤Zero  = Neg≤Zero
Zero≤Zero ⊚⸢≤ᶻ⸣ Zero≤Zero = Zero≤Zero
Zero≤Pos  ⊚⸢≤ᶻ⸣ Neg≤Zero  = Neg≤Pos
Zero≤Pos  ⊚⸢≤ᶻ⸣ Zero≤Zero = Zero≤Pos
Pos≤Pos g ⊚⸢≤ᶻ⸣ Neg≤Pos   = Neg≤Pos
Pos≤Pos g ⊚⸢≤ᶻ⸣ Zero≤Pos  = Zero≤Pos
Pos≤Pos g ⊚⸢≤ᶻ⸣ Pos≤Pos f = Pos≤Pos (g ⊚ f)

⋈⸢≤ᶻ⸣ : antisymmetric _≤ᶻ_
⋈⸢≤ᶻ⸣ (Neg≤Neg f) (Neg≤Neg g) = res[•x] (⋈ g f)
⋈⸢≤ᶻ⸣ Neg≤Zero ()
⋈⸢≤ᶻ⸣ Neg≤Pos ()
⋈⸢≤ᶻ⸣ Zero≤Zero Zero≤Zero = ↯
⋈⸢≤ᶻ⸣ Zero≤Pos ()
⋈⸢≤ᶻ⸣ (Pos≤Pos f) (Pos≤Pos g) = res[•x] (⋈ f g)

data _<ᶻ_ : ℤ → ℤ → Set where
  Neg<Neg : ∀ {n₁ n₂} → n₂ <ⁿ n₁ → Neg n₁ <ᶻ Neg n₂
  Neg<Zero : ∀ {n₁} → Neg n₁ <ᶻ Zero
  Neg<Pos : ∀ {n₁ n₂} → Neg n₁ <ᶻ Pos n₂
  Zero<Pos : ∀ {n₂} → Zero <ᶻ Pos n₂
  Pos<Pos : ∀ {n₁ n₂} → n₁ < n₂ → Pos n₁ <ᶻ Pos n₂

weaken[<]ᶻ : ∀ {i₁ i₂} → i₁ <ᶻ i₂ → i₁ ≤ᶻ i₂
weaken[<]ᶻ (Neg<Neg i₂<i₁) = Neg≤Neg (weaken[<][ ℕ ] i₂<i₁)
weaken[<]ᶻ Neg<Zero = Neg≤Zero
weaken[<]ᶻ Neg<Pos = Neg≤Pos
weaken[<]ᶻ Zero<Pos = Zero≤Pos
weaken[<]ᶻ (Pos<Pos i₁<i₂) = Pos≤Pos (weaken[<][ ℕ ] i₁<i₂)

strict[<]ᶻ : ∀ {i₁ i₂} → i₁ <ᶻ i₂ → ¬ (i₂ ≤ᶻ i₁)
strict[<]ᶻ (Neg<Neg i₂<i₁) (Neg≤Neg i₁≤i₂) = strict[<][ ℕ ] i₂<i₁ i₁≤i₂
strict[<]ᶻ Neg<Zero ()
strict[<]ᶻ Neg<Pos ()
strict[<]ᶻ Zero<Pos ()
strict[<]ᶻ (Pos<Pos i₁<i₂) (Pos≤Pos i₂≤i₁) = strict[<][ ℕ ] i₁<i₂ i₂≤i₁

complete[<]ᶻ : ∀ {i₁ i₂} → i₁ ≤ᶻ i₂ → ¬ (i₂ ≤ᶻ i₁) → i₁ <ᶻ i₂
complete[<]ᶻ (Neg≤Neg i₁≤i₂) ¬≤ = Neg<Neg (complete[<][ ℕ ] i₁≤i₂ (λ n₁≤n₂ → ¬≤ (Neg≤Neg n₁≤n₂)))
complete[<]ᶻ Neg≤Zero ¬≤ = Neg<Zero
complete[<]ᶻ Neg≤Pos ¬≤ = Neg<Pos
complete[<]ᶻ Zero≤Zero ¬≤ = exfalso (¬≤ Zero≤Zero)
complete[<]ᶻ Zero≤Pos ¬≤ = Zero<Pos
complete[<]ᶻ (Pos≤Pos i₁≤i₂) ¬≤ = Pos<Pos (complete[<][ ℕ ] i₁≤i₂ (λ n₂≤n₁ → ¬≤ (Pos≤Pos n₂≤n₁)))

_⋚ᶻ_ : ℤ → ℤ → ⪥!
Neg n₁ ⋚ᶻ Neg n₂ with n₁ ⋚ n₂
… | [<] = [>]
… | [≡] = [≡]
… | [>] = [<]
Neg n₁ ⋚ᶻ Zero = [<]
Neg n₁ ⋚ᶻ Pos n₂ = [<]
Zero ⋚ᶻ Neg n₂ = [>]
Zero ⋚ᶻ Zero = [≡]
Zero ⋚ᶻ Pos n₂ = [<]
Pos n₁ ⋚ᶻ Neg n₂ = [>]
Pos n₁ ⋚ᶻ Zero = [>]
Pos n₁ ⋚ᶻ Pos n₂ = n₁ ⋚ n₂

_⋚ᶻᴾ_ : ∀ i₁ i₂ → i₁ ⪥!ᴾ[ _<ᶻ_ ] i₂
Neg n₁ ⋚ᶻᴾ Neg n₂ with n₁ ⋚ᴾ n₂
… | [<] n₁<n₂ = [>] (Neg<Neg n₁<n₂)
… | [≡] n₁≡n₂ rewrite n₁≡n₂ = [≡] ↯
… | [>] n₁>n₂ = [<] (Neg<Neg n₁>n₂)
Neg n₁ ⋚ᶻᴾ Zero = [<] Neg<Zero
Neg n₁ ⋚ᶻᴾ Pos n₂ = [<] Neg<Pos
Zero ⋚ᶻᴾ Neg n₂ = [>] Neg<Zero
Zero ⋚ᶻᴾ Zero = [≡] ↯
Zero ⋚ᶻᴾ Pos n₂ = [<] Zero<Pos
Pos n₁ ⋚ᶻᴾ Neg n₂ = [>] Neg<Pos
Pos n₁ ⋚ᶻᴾ Zero = [>] Zero<Pos
Pos n₁ ⋚ᶻᴾ Pos n₂ with n₁ ⋚ᴾ n₂
… | [<] n₁<n₂ = [<] (Pos<Pos n₁<n₂)
… | [≡] n₁≡n₂ rewrite n₁≡n₂ = [≡] ↯
… | [>] n₁>n₂ = [>] (Pos<Pos n₁>n₂)

_⋚ᶻᴸ_ : ∀ i₁ i₂ → i₁ ⪥!ᴸ[ _<ᶻ_ ] i₂ ‖[ i₁ ⋚ᶻ i₂ , i₁ ⋚ᶻᴾ i₂ ]
Neg n₁ ⋚ᶻᴸ Neg n₂ with n₁ ⋚ n₂ | n₁ ⋚ᴾ n₂ | n₁ ⋚ᴸ n₂
… | [<] | [<] n₁<n₂ | [<] = [>]
… | [≡] | [≡] n₁≡n₂ | [≡] rewrite n₁≡n₂ = [≡]
… | [>] | [>] n₁>n₂ | [>] = [<]
Neg n₁ ⋚ᶻᴸ Zero = [<]
Neg n₁ ⋚ᶻᴸ Pos n₂ = [<]
Zero ⋚ᶻᴸ Neg n₂ = [>]
Zero ⋚ᶻᴸ Zero = [≡]
Zero ⋚ᶻᴸ Pos n₂ = [<]
Pos n₁ ⋚ᶻᴸ Neg n₂ = [>]
Pos n₁ ⋚ᶻᴸ Zero = [>]
Pos n₁ ⋚ᶻᴸ Pos n₂ with n₁ ⋚ n₂ | n₁ ⋚ᴾ n₂ | n₁ ⋚ᴸ n₂
… | [<] | [<] n₁<n₂ | [<] = [<]
… | [≡] | [≡] n₁≡n₂ | [≡] rewrite n₁≡n₂ = [≡]
… | [>] | [>] n₁>n₂ | [>] = [>]

instance
  Reflexive[≤]ᶻ : Reflexive _≤ᶻ_
  Reflexive[≤]ᶻ = record { xRx = xRx⸢≤ᶻ⸣ }
  Transitive[≤]ᶻ : Transitive _≤ᶻ_
  Transitive[≤]ᶻ = record { _⊚_ = _⊚⸢≤ᶻ⸣_ }
  Antisymmetric[≤]ᶻ : Antisymmetric _≤ᶻ_
  Antisymmetric[≤]ᶻ = record { ⋈ = ⋈⸢≤ᶻ⸣ }
  Strict[<]ᶻ : Strict _≤ᶻ_ _<ᶻ_
  Strict[<]ᶻ = record
    { weaken[≺] = weaken[<]ᶻ
    ; strict[≺] = strict[<]ᶻ
    ; complete[≺] = complete[<]ᶻ
    }
  Irreflexive[<]ᶻ : Irreflexive _<ᶻ_
  Irreflexive[<]ᶻ = Irreflexive[<]/≤ _≤ᶻ_ _<ᶻ_
  Transitive[<]ᶻ : Transitive _<ᶻ_
  Transitive[<]ᶻ = Transitive[<]/≤ _≤ᶻ_ _<ᶻ_
  Asymmetric[<]ᶻ : Asymmetric _<ᶻ_
  Asymmetric[<]ᶻ = Asymmetric[<]/≤ _≤ᶻ_ _<ᶻ_
  Totally[<]ᶻ : Totally _<ᶻ_
  Totally[<]ᶻ = record
    { _⪥_ = _⋚ᶻ_
    ; _⪥ᴾ_ = _⋚ᶻᴾ_
    ; _⪥ᴸ_ = _⋚ᶻᴸ_
    }
  Order[ℤ] : Order 0ᴸ ℤ
  Order[ℤ] = mk[Order] _≤ᶻ_ _<ᶻ_

------------------
-- ≡ᶻ Decidable --
------------------

instance
  DecRel[≡]ᶻ : DecRel (_≡_ {A = ℤ})
  DecRel[≡]ᶻ = record
    { _⁇_ = ⁇[≡]/⪥[] _≤_ _<_
    ; _⁇ᴾ_ = ⁇ᴾ[≡]/⪥[] _≤_ _<_
    ; _⁇ᴸ_ = ⁇ᴸ[≡]/⪥[] _≤_ _<_
    }
  DecEqᶻ : DecEq ℤ
  DecEqᶻ = record {}
  DecRel[≤]ᶻ : DecRel _≤ᶻ_
  DecRel[≤]ᶻ = record
    { _⁇_ = ⁇[≤]/⪥[] _≤_ _<_
    ; _⁇ᴾ_ = ⁇ᴾ[≤]/⪥[] _≤_ _<_
    ; _⁇ᴸ_ = ⁇ᴸ[≤]/⪥[] _≤_ _<_
    }
  DecLteᶻ : DecLte ℤ
  DecLteᶻ = record {}
  DecRel[<]ᶻ : DecRel _<ᶻ_
  DecRel[<]ᶻ = record
    { _⁇_ = ⁇[<]/⪥[] _≤_ _<_
    ; _⁇ᴾ_ = ⁇ᴾ[<]/⪥[] _≤_ _<_
    ; _⁇ᴸ_ = ⁇ᴸ[<]/⪥[] _≤_ _<_
    }
  DecLtᶻ : DecLt ℤ
  DecLtᶻ = record {}
  
-----------
-- Signs --
-----------

data signᶻ : Set where Zero [-] [+] : signᶻ

‖_‖ : ℤ → ℕ
‖ Neg n ‖ = Succ n
‖ Zero  ‖ = Zero
‖ Pos n ‖ = Succ n

signofᶻ : ℤ → signᶻ
signofᶻ (Neg _) = [-]
signofᶻ Zero = Zero
signofᶻ (Pos _) = [+]

correct[‖‖] : ∀ n → ‖ 𝕫 n ‖ ≡ n
correct[‖‖] Zero = ↯
correct[‖‖] (Succ n) = ↯

⁻ᶻ_ : ℤ → ℤ
⁻ᶻ Neg n = Pos n
⁻ᶻ Zero = Zero
⁻ᶻ Pos n = Neg n

-------------------------------
-- Successor and Predecessor --
-------------------------------

sucᶻ : ℤ → ℤ
sucᶻ (Neg Zero) = Zero
sucᶻ (Neg (Succ n)) = Neg n
sucᶻ Zero = Pos Zero
sucᶻ (Pos n) = Pos (Succ n)

predᶻ : ℤ → ℤ
predᶻ (Neg n) = Neg (Succ n)
predᶻ Zero = Neg Zero
predᶻ (Pos Zero) = Zero
predᶻ (Pos (Succ n)) = Pos n

pred∘succ=id : ∀ i → predᶻ (sucᶻ i) ≡ i
pred∘succ=id (Neg Zero) = ↯
pred∘succ=id (Neg (Succ n)) = ↯
pred∘succ=id Zero = ↯
pred∘succ=id (Pos Zero) = ↯
pred∘succ=id (Pos (Succ n)) = ↯

succ∘pred=id : ∀ i → sucᶻ (predᶻ i) ≡ i
succ∘pred=id (Neg Zero) = ↯
succ∘pred=id (Neg (Succ n)) = ↯
succ∘pred=id Zero = ↯
succ∘pred=id (Pos Zero) = ↯
succ∘pred=id (Pos (Succ n)) = ↯

--------------
-- Addition --
--------------

_+ᶻ_ : ℤ → ℤ → ℤ
Zero +ᶻ j = j
i +ᶻ Zero = i
Neg n₁ +ᶻ Neg n₂ = Neg (Succ (n₁ + n₂))
Pos n₁ +ᶻ Pos n₂ = Pos (Succ (n₁ + n₂))
Neg n₁ +ᶻ Pos n₂ with n₁ -%ⁿ n₂
… | Inl Zero = Zero
… | Inl (Succ n) = Neg n
… | Inr Zero = Zero
… | Inr (Succ n) = Pos n
Pos n₁ +ᶻ Neg n₂ with n₁ -%ⁿ n₂
… | Inl Zero = Zero
… | Inl (Succ n) = Pos n
… | Inr Zero = Zero
… | Inr (Succ n) = Neg n

left-unit[+ᶻ] : ∀ i → Zero +ᶻ i ≡ i
left-unit[+ᶻ] (Neg n) = ↯
left-unit[+ᶻ] Zero = ↯
left-unit[+ᶻ] (Pos n) = ↯

right-unit[+ᶻ] : ∀ i → i +ᶻ Zero ≡ i
right-unit[+ᶻ] (Neg n) = ↯
right-unit[+ᶻ] Zero = ↯
right-unit[+ᶻ] (Pos n) = ↯

postulate
  associative[+ᶻ] : ∀ i j k → (i +ᶻ j) +ᶻ k ≡ i +ᶻ (j +ᶻ k)
  commutative[+ᶻ] : ∀ i j → i +ᶻ j ≡ j +ᶻ i

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

_-ᶻ_ : ℤ → ℤ → ℤ
i₁ -ᶻ i₂ = i₁ +ᶻ (⁻ᶻ i₂)

postulate
  correct[-ᶻ] : ∀ i j → i +ᶻ (j -ᶻ i) ≡ j

instance
  Subtractive[ℤ] : Subtractive ℤ
  Subtractive[ℤ] = record
    { _-_ = _-ᶻ_
    ; correct[-] = correct[-ᶻ]
    }

--------------------
-- Multiplication --
--------------------

_×ᶻ_ : ℤ → ℤ → ℤ
Zero ×ᶻ j = Zero
i ×ᶻ Zero = Zero
Neg n₁ ×ᶻ Neg n₂ = 𝕫 (Succ n₁ × Succ n₂ 𝑎𝑡 ℕ)
Pos n₁ ×ᶻ Pos n₂ = 𝕫 (Succ n₁ × Succ n₂ 𝑎𝑡 ℕ)
Neg n₁ ×ᶻ Pos n₂ = ⁻ 𝕫 (Succ n₁ × Succ n₂ 𝑎𝑡 ℕ)
Pos n₁ ×ᶻ Neg n₂ = ⁻ 𝕫 (Succ n₁ × Succ n₂ 𝑎𝑡 ℕ)

postulate
  left-zero[×]ᶻ : ∀ i → 𝕫 0 ×ᶻ i ≡ 𝕫 0
  right-zero[×]ᶻ : ∀ i → i ×ᶻ 𝕫 0 ≡ 𝕫 0
  left-unit[×]ᶻ : ∀ i → 𝕫 1 ×ᶻ i ≡ i
  right-unit[×]ᶻ : ∀ i → i ×ᶻ 𝕫 1 ≡ i
  distributive[×]ᶻ : ∀ i j k → (i + j) ×ᶻ k ≡ (i ×ᶻ k) + (j ×ᶻ k)
  associative[×]ᶻ : ∀ i j k → (i ×ᶻ j) ×ᶻ k ≡ i ×ᶻ (j ×ᶻ k)
  commutative[×]ᶻ : ∀ i j → i ×ᶻ j ≡ j ×ᶻ i

instance
  Multiplicative[ℤ] : Multiplicative ℤ
  Multiplicative[ℤ] = record
    { one = 𝕫 1
    ; _×_ = _×ᶻ_
    ; left-zero[×] = left-zero[×]ᶻ
    ; right-zero[×] = right-zero[×]ᶻ
    ; left-unit[×] = left-unit[×]ᶻ
    ; right-unit[×] = right-unit[×]ᶻ
    ; associative[×] = associative[×]ᶻ
    ; commutative[×] = commutative[×]ᶻ
    ; distributive[×] = distributive[×]ᶻ
    }

--------------
-- Division --
--------------

_/%ᶻ_‖_ : ∀ (i j : ℤ) → j ≢ 𝕫 0 → ℤ ∧ ℤ
Zero /%ᶻ j ‖ p = ⟨ Zero , Zero ⟩
i /%ᶻ Zero ‖ p = exfalso $ p ↯
Neg n /%ᶻ Neg m ‖ p with Succ n /%ⁿ Succ m ‖ Zero
… | ⟨ quotient , remainder ⟩ = ⟨ 𝕫 quotient , ⁻ᶻ 𝕫 remainder ⟩
Neg n /%ᶻ Pos m ‖ p with Succ n /%ⁿ Succ m ‖ Zero
… | ⟨ quotient , remainder ⟩ = ⟨ ⁻ᶻ 𝕫 quotient , ⁻ᶻ 𝕫 remainder ⟩
Pos n /%ᶻ Neg m ‖ p with Succ n /%ⁿ Succ m ‖ Zero
… | ⟨ quotient , remainder ⟩ = ⟨ ⁻ᶻ 𝕫 quotient , 𝕫 remainder ⟩
Pos n /%ᶻ Pos m ‖ p with Succ n /%ⁿ Succ m ‖ Zero
… | ⟨ quotient , remainder ⟩ = ⟨ 𝕫 quotient , 𝕫 remainder ⟩

-- test-%/ᶻ-1 : (𝕫 8 /%ᶻ 𝕫 6 ‖ ↯¬rel) ≡ ⟨ 𝕫ⁿ 1 , 𝕫ⁿ 2 ⟩
-- test-%/ᶻ-1 = ↯

-- test-%/ᶻ-2 : ((⁻ᶻ 𝕫 8) /%ᶻ 𝕫 6 ‖ ↯¬rel) ≡ ⟨ ⁻ᶻ 𝕫ⁿ 1 , ⁻ᶻ 𝕫ⁿ 2 ⟩
-- test-%/ᶻ-2 = ↯

-- test-%/ᶻ-3 : (𝕫 8 /%ᶻ ⁻ᶻ 𝕫 6 ‖ ↯¬rel) ≡ ⟨ ⁻ᶻ 𝕫ⁿ 1 , 𝕫ⁿ 2 ⟩
-- test-%/ᶻ-3 = ↯

-- test-%/ᶻ-4 : ((⁻ᶻ 𝕫 8) /%ᶻ ⁻ᶻ 𝕫 6 ‖ ↯¬rel) ≡ ⟨ 𝕫ⁿ 1 , ⁻ᶻ 𝕫ⁿ 2 ⟩
-- test-%/ᶻ-4 = ↯

postulate
  correct[/%‖]ᶻ : ∀ i j (j≢0 : j ≢ 𝕫 0) → let ⟨ quo , rem ⟩ = i /%ᶻ j ‖ j≢0 in (j ×ᶻ quo) +ᶻ rem ≡ i

instance
  DivMod/OK[ℤ] : DivMod/OK ℤ
  DivMod/OK[ℤ] = record
    { ok[_/%_] = (λ i j → j ≢ 𝕫 0) }
  DivMod[ℤ] : DivMod/P ℤ
  DivMod[ℤ] = record
    { _/%_‖_ = _/%ᶻ_‖_
    ; correct[/%‖] = correct[/%‖]ᶻ
    }

-------------
-- Bounded --
-------------

record ℤ⁺ : Set 0ᴸ where
  constructor mk[ℤ⁺]
  field
    i : ℤ
    i≠0 : i ≢ Zero
   
-- mk↯[ℤ⁺] : ∀ (i : ℤ) → {{IY : ¬rel (dec-rel[ _≡_ ] i Zero)}} → ℤ⁺
-- mk↯[ℤ⁺] i {{_}} with dec-rel[ _≡_ ] i Zero
-- mk↯[ℤ⁺] i {{↯Rel}} | ¬Rel i≠0 = mk[ℤ⁺] i i≠0
