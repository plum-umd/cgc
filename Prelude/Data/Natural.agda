module Prelude.Data.Natural where

open import Prelude.Core
open import Prelude.Relations
open import Prelude.Classes

infix  14 _≤ⁿ_
infixr 22 _+ⁿ_
infixr 23 _-ⁿ_‖_
infixr 24 _×ⁿ_

----------------
-- Conversion --
----------------

record ToNatural {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mk[ToNatural]
  field
    𝕟 : A → ℕ
open ToNatural {{...}}

-------------
-- ≤ Order --
-------------

data _≤ⁿ_ : ℕ → ℕ → Set where
  Zero : ∀ {n} → Zero ≤ⁿ n
  Succ : ∀ {n₁ n₂} → n₁ ≤ⁿ n₂ → Succ n₁ ≤ⁿ Succ n₂

_<ⁿ_ : relation 0ᴸ ℕ
n₁ <ⁿ n₂ = Succ n₁ ≤ⁿ n₂

xRx⸢≤ⁿ⸣ : reflexive _≤ⁿ_
xRx⸢≤ⁿ⸣ {Zero} = Zero
xRx⸢≤ⁿ⸣ {Succ n} = Succ xRx⸢≤ⁿ⸣

_⊚⸢≤ⁿ⸣_ : transitive _≤ⁿ_
n₁≤n₂ ⊚⸢≤ⁿ⸣ Zero = Zero
Succ n₂≤n₃ ⊚⸢≤ⁿ⸣ Succ n₁≤n₂ = Succ (n₂≤n₃ ⊚⸢≤ⁿ⸣ n₁≤n₂)

⋈⸢≤ⁿ⸣ : antisymmetric _≤ⁿ_
⋈⸢≤ⁿ⸣ Zero Zero = ↯
⋈⸢≤ⁿ⸣ (Succ n₁≤n₂) (Succ n₂≤n₁) = res[•x] $ ⋈⸢≤ⁿ⸣ n₁≤n₂ n₂≤n₁

_⋚ⁿ_ : dec-total-order _≡_ _≤ⁿ_
Zero   ⋚ⁿ Zero   = [~] ↯
Zero   ⋚ⁿ Succ n₂ = [<] Zero (λ ())
Succ n₁ ⋚ⁿ Zero   = [>] Zero (λ ())
Succ n₁ ⋚ⁿ Succ n₂ with n₁ ⋚ⁿ n₂
... | [<] n₁≤n₂ not[n₂≤n₁] = [<] (Succ n₁≤n₂) BAD
  where
    BAD : Succ n₂ ≤ⁿ Succ n₁ → void
    BAD (Succ n₂≤n₁) = not[n₂≤n₁] n₂≤n₁
... | [~] n₁≡n₂ = [~] (res[•x] n₁≡n₂)
... | [>] n₁≥n₂ not[n₂≥n₁] = [>] (Succ n₁≥n₂) BAD
  where
    BAD : Succ n₁ ≤ⁿ Succ n₂ → void
    BAD (Succ n₂≥n₁) = not[n₂≥n₁] n₂≥n₁

weaken[n≤n] : ∀ {n₁ n₂ : ℕ} → n₁ ≤ⁿ n₂ → n₁ ≤ⁿ Succ n₂
weaken[n≤n] Zero = Zero
weaken[n≤n] (Succ n₁≤n₂) = Succ (weaken[n≤n] n₁≤n₂)

weaken[succ≤n] : ∀ {n₁ n₂ : ℕ} → Succ n₁ ≤ⁿ n₂ → n₁ ≤ⁿ n₂
weaken[succ≤n] (Succ n₁≤pred[n₂]) = weaken[n≤n] n₁≤pred[n₂]

¬succ≤n : ∀ {n : ℕ} → not (Succ n ≤ⁿ n)
¬succ≤n {Zero} ()
¬succ≤n {Succ n} (Succ n≤pred[n]) = ¬succ≤n n≤pred[n]

correct[<ⁿ] : ∀ {n₁ n₂} → n₁ <ⁿ n₂ ↔ n₁ ≤ⁿ n₂ ∧ not (n₂ ≤ⁿ n₁)
correct[<ⁿ] = LHS , RHS
  where
    LHS : ∀ {n₁ n₂ : ℕ} → n₁ <ⁿ n₂ → n₁ ≤ⁿ n₂ ∧ not (n₂ ≤ⁿ n₁)
    LHS (Succ n₁≤pred[n₂]) = weaken[n≤n] n₁≤pred[n₂] , (λ n₁≤n₂ → ¬succ≤n (n₁≤pred[n₂] ⊚⸢≤ⁿ⸣ n₁≤n₂))
    RHS : ∀ {n₁ n₂ : ℕ} → n₁ ≤ⁿ n₂ ∧ not (n₂ ≤ⁿ n₁) → n₁ <ⁿ n₂
    RHS {n₂ = Zero} (n₁≤n₂ , n₂≤/n₁) = exfalso $ n₂≤/n₁ Zero
    RHS {n₂ = Succ pred[n₂]} (Zero , n₂≤/n₁) = Succ Zero
    RHS {n₂ = Succ pred[n₂]} (Succ n₁≤n₂ , n₂≤/n₁) = Succ (RHS (n₁≤n₂ , (λ pred[n₂]≤n₁ → n₂≤/n₁ (Succ pred[n₂]≤n₁))))

n≤suc : ∀ {n : ℕ} → n ≤ⁿ Succ n
n≤suc = weaken[n≤n] xRx⸢≤ⁿ⸣

instance
  Reflexive[≤ⁿ] : Reflexive _≤ⁿ_
  Reflexive[≤ⁿ] = record { xRx = xRx⸢≤ⁿ⸣ }
  Transitive[≤ⁿ] : Transitive _≤ⁿ_
  Transitive[≤ⁿ] = record { _⊚_ = _⊚⸢≤ⁿ⸣_ }
  Antisymmetric[≤ⁿ] : Antisymmetric _≤ⁿ_
  Antisymmetric[≤ⁿ] = record { ⋈ = ⋈⸢≤ⁿ⸣ }
  TotalOrder[ℕ] : TotalOrder 0ᴸ ℕ
  TotalOrder[ℕ] = record
    { _≤_ = _≤ⁿ_
    ; _<_ = _<ⁿ_
    ; correct[<] = correct[<ⁿ]
    ; _⋚_ = _⋚ⁿ_
    ; Reflexive[≤] = Reflexive[≤ⁿ]
    ; Transitive[≤] = Transitive[≤ⁿ]
    ; Antisymmetric[≤] = Antisymmetric[≤ⁿ]
    }

------------------
-- ≤ⁿ Decidable --
------------------

dec[≤ⁿ] : dec-rel _≤ⁿ_
dec[≤ⁿ] n₁ n₂ with n₁ ⋚ n₂
... | [<] n₁≤n₂ _ = Yes n₁≤n₂
... | [~] n₁≡n₂ = Yes (xRx[≡] n₁≡n₂)
... | [>] _ not[n₁≥n₂] = No not[n₁≥n₂]

instance
  RelDec⸢≤ⁿ⸣ : DecRel _≤ⁿ_
  RelDec⸢≤ⁿ⸣ = record { dec[] = dec[≤ⁿ] }

--------------
-- Addition --
--------------

_+ⁿ_ : ℕ → ℕ → ℕ
Zero +ⁿ n₂ = n₂
Succ n₁ +ⁿ n₂ = Succ (n₁ +ⁿ n₂)

left-unit[+ⁿ] : ∀ (n : ℕ) → 0 +ⁿ n ≡ n
left-unit[+ⁿ] n = ↯

right-unit[+ⁿ] : ∀ (n : ℕ) → n +ⁿ 0 ≡ n
right-unit[+ⁿ] Zero = ↯
right-unit[+ⁿ] (Succ n) rewrite right-unit[+ⁿ] n = ↯

associative[+ⁿ] : ∀ (n₁ n₂ n₃ : ℕ) → (n₁ +ⁿ n₂) +ⁿ n₃ ≡ n₁ +ⁿ n₂ +ⁿ n₃
associative[+ⁿ] Zero n₂ n₃ = ↯
associative[+ⁿ] (Succ n₁) n₂ n₃ rewrite associative[+ⁿ] n₁ n₂ n₃ = ↯

m+suc[n]=suc[m+n] : ∀ (n₁ n₂ : ℕ) → n₁ +ⁿ Succ n₂ ≡ Succ (n₁ +ⁿ n₂)
m+suc[n]=suc[m+n] Zero n₂ = ↯
m+suc[n]=suc[m+n] (Succ n₁) n₂ rewrite m+suc[n]=suc[m+n] n₁ n₂ = ↯

suc[m+n]=m+suc[n] : ∀ (n₁ n₂ : ℕ) → Succ (n₁ +ⁿ n₂) ≡ n₁ +ⁿ Succ n₂
suc[m+n]=m+suc[n] n₁ n₂ = ◇ $ m+suc[n]=suc[m+n] n₁ n₂

commutative[+ⁿ] : ∀ (n₁ n₂ : ℕ) → n₁ +ⁿ n₂ ≡ n₂ +ⁿ n₁
commutative[+ⁿ] Zero n₂ rewrite right-unit[+ⁿ] n₂ = ↯
commutative[+ⁿ] (Succ n₁) n₂ rewrite commutative[+ⁿ] n₁ n₂ | suc[m+n]=m+suc[n] n₂ n₁ = ↯

instance
  Additive[ℕ] : Additive ℕ
  Additive[ℕ] = record
    { zero = Zero
    ; _+_ = _+ⁿ_
    ; left-unit[+] = left-unit[+ⁿ]
    ; right-unit[+] = right-unit[+ⁿ]
    ; associative[+] = associative[+ⁿ]
    ; commutative[+] = commutative[+ⁿ]
    }

--------------------
-- Multiplication --
--------------------

oneⁿ : ℕ
oneⁿ = Succ Zero

_×ⁿ_ : ℕ → ℕ → ℕ
Zero ×ⁿ n₂ = Zero
Succ n₁ ×ⁿ n₂ = n₂ +ⁿ n₁ ×ⁿ n₂

left-zero[×ⁿ] : ∀ n → zero ×ⁿ n ≡ zero
left-zero[×ⁿ] n = ↯

right-zero[×ⁿ] : ∀ n → n ×ⁿ zero ≡ zero
right-zero[×ⁿ] Zero = ↯
right-zero[×ⁿ] (Succ n) rewrite right-zero[×ⁿ] n = ↯

left-unit[×ⁿ] : ∀ n → oneⁿ ×ⁿ n ≡ n
left-unit[×ⁿ] n = right-unit[+ⁿ] n

right-unit[×ⁿ] : ∀ n → n ×ⁿ oneⁿ ≡ n
right-unit[×ⁿ] Zero = ↯
right-unit[×ⁿ] (Succ n) rewrite right-unit[×ⁿ] n = ↯

distributive[×ⁿ] : ∀ n₁ n₂ n₃ → (n₁ +ⁿ n₂) ×ⁿ n₃ ≡ n₁ ×ⁿ n₃ +ⁿ n₂ ×ⁿ n₃
distributive[×ⁿ] Zero n₂ n₃ = ↯
distributive[×ⁿ] (Succ n₁) n₂ n₃ rewrite distributive[×ⁿ] n₁ n₂ n₃ | associative[+ⁿ] n₃ (n₁ ×ⁿ n₃) (n₂ ×ⁿ n₃) = ↯

associative[×ⁿ] : ∀ n₁ n₂ n₃ → (n₁ ×ⁿ n₂) ×ⁿ n₃ ≡ n₁ ×ⁿ (n₂ ×ⁿ n₃)
associative[×ⁿ] Zero n₂ n₃ = ↯
associative[×ⁿ] (Succ n₁) n₂ n₃ rewrite distributive[×ⁿ] n₂ (n₁ ×ⁿ n₂) n₃ | associative[×ⁿ] n₁ n₂ n₃ = ↯

commutative[×ⁿ] : ∀ n₁ n₂ → n₁ ×ⁿ n₂ ≡ n₂ ×ⁿ n₁
commutative[×ⁿ] Zero n₂ rewrite right-zero[×ⁿ] n₂ = ↯
commutative[×ⁿ] n₁ Zero rewrite right-zero[×ⁿ] n₁ = ↯
commutative[×ⁿ] (Succ n₁) (Succ n₂)
  rewrite commutative[×ⁿ] n₁ (Succ n₂)
        | commutative[×ⁿ] n₂ (Succ n₁)
        | commutative[×ⁿ] n₁ n₂
        | ◇ $ associative[+ⁿ] n₁ n₂ (n₂ ×ⁿ n₁)
        | commutative[+ⁿ] n₁ n₂
        | associative[+ⁿ] n₂ n₁ (n₂ ×ⁿ n₁)
        = ↯

instance
  Multiplicative[ℕ] : Multiplicative ℕ
  Multiplicative[ℕ] = record
    { one = oneⁿ
    ; _×_ = _×ⁿ_
    ; left-zero[×] = left-zero[×ⁿ]
    ; right-zero[×] = right-zero[×ⁿ]
    ; left-unit[×] = left-unit[×ⁿ]
    ; right-unit[×] = right-unit[×ⁿ]
    ; associative[×] = associative[×ⁿ]
    ; commutative[×] = commutative[×ⁿ]
    ; distributive[×] = distributive[×ⁿ]
    }

-----------------
-- Subtraction --
-----------------

_-ⁿ_‖_ : ∀ (n₁ n₂ : ℕ) → n₂ ≤ n₁ → ℕ
n₁ -ⁿ Zero ‖ Zero = n₁
Succ n₁ -ⁿ Succ n₂ ‖ Succ n₁≤n₂ = n₁ -ⁿ n₂ ‖ n₁≤n₂

correct[-ⁿ‖] : ∀ n₁ n₂ (n₂≤n₁ : n₂ ≤ n₁) → n₂ + (n₁ -ⁿ n₂ ‖ n₂≤n₁) ≡ n₁
correct[-ⁿ‖] n₁ Zero Zero = ↯
correct[-ⁿ‖] (Succ n₁) (Succ n₂) (Succ n₂≤n₁) rewrite correct[-ⁿ‖] n₁ n₂ n₂≤n₁ = ↯

n-n=0 : ∀ n → n -ⁿ n ‖ xRx ≡ Zero
n-n=0 Zero = ↯
n-n=0 (Succ n) rewrite n-n=0 n = ↯

n-0=n : ∀ n → n -ⁿ 0 ‖ Zero ≡ n
n-0=n n = ↯

suc[m-n]=suc[m]-n : ∀ n₁ n₂ (n₂≤n₁ : n₂ ≤ n₁) → Succ (n₁ -ⁿ n₂ ‖ n₂≤n₁) ≡ Succ n₁ -ⁿ n₂ ‖ weaken[n≤n] n₂≤n₁
suc[m-n]=suc[m]-n n₁ Zero Zero = ↯
suc[m-n]=suc[m]-n (Succ n₁) (Succ n₂) (Succ n₂≤n₁) rewrite suc[m-n]=suc[m]-n n₁ n₂ n₂≤n₁ = ↯

instance
  Subtractive/OK[ℕ] : Subtractive/OK ℕ
  Subtractive/OK[ℕ] = record { ok[_-_] = _≥_ }
  Subtractive[ℕ] : Subtractive/P ℕ
  Subtractive[ℕ] = record
    { ok[x-x] = λ x → xRx
    ; _-_‖_ = _-ⁿ_‖_
    ; correct[-‖] = correct[-ⁿ‖]
    }

_-%ⁿ_ : ∀ (n₁ n₂ : ℕ) → ℕ ∨ ℕ
Zero -%ⁿ n₂ = Inr n₂
n₁ -%ⁿ Zero = Inl n₁
Succ n₁ -%ⁿ Succ n₂ = n₁ -%ⁿ n₂

correct[-%ⁿ]/spec : ℕ → ℕ → Set
correct[-%ⁿ]/spec n₁ n₂ with n₁ -%ⁿ n₂
... | Inl n = n₂ + n ≡ n₁
... | Inr n = n₁ + n ≡ n₂

correct[-%ⁿ] : ∀ n₁ n₂ → correct[-%ⁿ]/spec n₁ n₂
correct[-%ⁿ] Zero Zero = ↯
correct[-%ⁿ] Zero (Succ n₂) = ↯
correct[-%ⁿ] (Succ n₁) Zero = ↯
correct[-%ⁿ] (Succ n₁) (Succ n₂) with n₁ -%ⁿ n₂ | correct[-%ⁿ] n₁ n₂
... | Inl x | IH rewrite IH = ↯
... | Inr x | IH rewrite IH = ↯

--------------------------
-- Division and Modulus --
--------------------------

divmod-loop : ∀ (n₁ n₂ quo n₂-rem : ℕ) → n₂-rem ≤ n₂ → ∃ quo,n₂-rem ⦂ ℕ ∧ ℕ 𝑠𝑡 let quo' , n₂-rem' = quo,n₂-rem in n₂-rem' ≤ n₂
divmod-loop Zero n₂ quo n₂-rem n₂-rem≤n₂ = ∃ quo , n₂-rem ,, n₂-rem≤n₂
divmod-loop (Succ n₁) n₂ quo Zero n₂-rem≤n₂ = divmod-loop n₁ n₂ (Succ quo) n₂ xRx
divmod-loop (Succ n₁) n₂ quo (Succ n₂-rem) n₂-rem≤n₂ = divmod-loop n₁ n₂ quo n₂-rem (weaken[succ≤n] n₂-rem≤n₂)

correct[divmod-loop] :
  ∀ (n₁ n₂ quo n₂-rem : ℕ) (n₂-rem≤n₂ : n₂-rem ≤ n₂)
  → let ∃ quo' , n₂-rem' ,, n₂-rem'≤n₂ = divmod-loop n₁ n₂ quo n₂-rem n₂-rem≤n₂ in 
    quo' × Succ n₂ + (n₂ - n₂-rem' ‖ n₂-rem'≤n₂) ≡ n₁ + (quo × Succ n₂) + (n₂ - n₂-rem ‖ n₂-rem≤n₂)
correct[divmod-loop] Zero n₂ quo n₂-rem n₂-rem≤n₂ = ↯
correct[divmod-loop] (Succ n₁) n₂ quo Zero Zero
  with divmod-loop n₁ n₂ (Succ quo) n₂ xRx
     | correct[divmod-loop] n₁ n₂ (Succ quo) n₂ xRx
... | ∃ quo' , n₂-rem' ,, n₂-rem'≤n₂ | IH
  rewrite suc[m+n]=m+suc[n] n₁ (quo × Succ n₂ + n₂ - Zero ‖ Zero)
        | n-n=0 n₂
        | commutative[+] (quo × Succ n₂) n₂
        | right-unit[+] (n₂ + quo × Succ n₂)
        = IH
correct[divmod-loop] (Succ n₁) (Succ n₂) quo (Succ n₂-rem) (Succ n₂-rem≤n₂)
  with divmod-loop n₁ (Succ n₂) quo n₂-rem (weaken[n≤n] n₂-rem≤n₂)
     | correct[divmod-loop] n₁ (Succ n₂) quo n₂-rem (weaken[n≤n] n₂-rem≤n₂)
... | ∃ quo' , n₂-rem' ,, n₂-rem'≤n₂ | IH 
  rewrite suc[m+n]=m+suc[n] n₁ (quo × Succ (Succ n₂) + n₂ - n₂-rem ‖ n₂-rem≤n₂)
        | suc[m+n]=m+suc[n] (quo × Succ (Succ n₂)) (n₂ - n₂-rem ‖ n₂-rem≤n₂)
        | suc[m-n]=suc[m]-n n₂ n₂-rem n₂-rem≤n₂
        = IH

_/%ⁿ_‖_ : ∀ (n₁ n₂ : ℕ) (0<n₂ : 0 < n₂) → ℕ ∧ ℕ
n₁ /%ⁿ Succ n₂ ‖ Succ 0<n₂ with divmod-loop n₁ n₂ 0 n₂ xRx⸢≤ⁿ⸣
... | ∃ quo , n₂-rem ,, n₂-rem≤n₂ = quo , n₂ - n₂-rem ‖ n₂-rem≤n₂

correct[/%‖ⁿ] : ∀ n₁ n₂ (0<n₂ : 0 < n₂) → let quo , rem = n₁ /%ⁿ n₂ ‖ 0<n₂ in n₂ × quo + rem ≡ n₁
correct[/%‖ⁿ] n₁ (Succ n₂) (Succ 0<n₂) with divmod-loop n₁ n₂ 0 n₂ xRx | correct[divmod-loop] n₁ n₂ 0 n₂ xRx
... | ∃ quo , n₂-rem ,, n₂-rem≤n₂ | H rewrite n-n=0 n₂ | right-unit[+] n₁ | commutative[×] quo (Succ n₂) = H

instance
  DivMod/OK[ℕ] : DivMod/OK ℕ
  DivMod/OK[ℕ] = record
    { ok[_/%_] = (λ n₁ n₂ → 0 < n₂) }
  DivMod[ℕ] : DivMod/P ℕ
  DivMod[ℕ] = record
    { _/%_‖_ = _/%ⁿ_‖_
    ; correct[/%‖] = correct[/%‖ⁿ]
    }

-------------
-- Bounded --
-------------

record ℕ≤[_] (nᵇ : ℕ) : Set where
  constructor mk[ℕ≤]
  field
    n : ℕ
    n≤nᵇ : n ≤ nᵇ

mk[ℕ≤]⸢↯⸣ : ∀ {nᵇ} n → {{IY : is-rel (dec[≤ⁿ] n nᵇ)}} → ℕ≤[ nᵇ ]
mk[ℕ≤]⸢↯⸣ {nᵇ} n {{IY}} with dec[≤ⁿ] n nᵇ
mk[ℕ≤]⸢↯⸣ {nᵇ} n {{↯Rel}} | Yes n≤nᵇ = mk[ℕ≤] n n≤nᵇ

weaken-ℕ≤ : ∀ {nᵇ₁ nᵇ₂} → nᵇ₁ ≤ nᵇ₂ → ℕ≤[ nᵇ₁ ] → ℕ≤[ nᵇ₂ ]
weaken-ℕ≤ nᵇ₁≤nᵇ₂ (mk[ℕ≤] n n≤nᵇ₁) = mk[ℕ≤] n (nᵇ₁≤nᵇ₂ ⊚ n≤nᵇ₁)

instance
  ToNatural[ℕ≤] : ∀ {nᵇ} → ToNatural ℕ≤[ nᵇ ]
  ToNatural[ℕ≤] = mk[ToNatural] ℕ≤[_].n

record ℕ<[_] (nᵇ : ℕ) : Set where
  constructor mk[ℕ<]
  field
    n : ℕ
    n<nᵇ : n < nᵇ
    
mk[ℕ<]⸢↯⸣ : ∀ {nᵇ} n → {{IY : is-rel (dec[≤ⁿ] (Succ n) nᵇ)}} → ℕ<[ nᵇ ]
mk[ℕ<]⸢↯⸣ {nᵇ} n {{IY}} with dec[≤ⁿ] (Succ n) nᵇ
mk[ℕ<]⸢↯⸣ {nᵇ} n {{↯Rel}} | Yes n<nᵇ = mk[ℕ<] n n<nᵇ

weaken-ℕ< : ∀ {nᵇ₁ nᵇ₂} → nᵇ₁ ≤ nᵇ₂ → ℕ<[ nᵇ₁ ] → ℕ<[ nᵇ₂ ]
weaken-ℕ< nᵇ₁≤nᵇ₂ (mk[ℕ<] n n<nᵇ₁) = mk[ℕ<] n (nᵇ₁≤nᵇ₂ ⊚ n<nᵇ₁)

instance
  ToNatural[ℕ<] : ∀ {nᵇ} → ToNatural ℕ<[ nᵇ ]
  ToNatural[ℕ<] = mk[ToNatural] ℕ<[_].n

data fin : ℕ → Set where
  Zero : ∀ {n} → fin (Succ n)
  Succ : ∀ {n} → fin n → fin (Succ n)

fin⸢<ⁿ⸣ : ∀ {nᵇ} n → n < nᵇ → fin nᵇ
fin⸢<ⁿ⸣ Zero (Succ n<nᵇ) = Zero
fin⸢<ⁿ⸣ (Succ n) (Succ n<nᵇ) = Succ (fin⸢<ⁿ⸣ n n<nᵇ)

fin⸢ℕ<⸣ : ∀ {nᵇ} → ℕ<[ nᵇ ] → fin nᵇ
fin⸢ℕ<⸣ (mk[ℕ<] n n<nᵇ) = fin⸢<ⁿ⸣ n n<nᵇ

record ℕ⁺ : Set where
  constructor mk[ℕ⁺]
  field
    n : ℕ
    0<n : 0 < n

mk[ℕ⁺]/↯ : ∀ n {{IY : is-rel (dec[≤ⁿ] (Succ 0) n)}} → ℕ⁺
mk[ℕ⁺]/↯ n {{IY}} with dec[≤ⁿ] (Succ 0) n
mk[ℕ⁺]/↯ n {{↯Rel}} | Yes 0<n = mk[ℕ⁺] n 0<n

instance
  ToNatural[ℕ⁺] : ToNatural ℕ⁺
  ToNatural[ℕ⁺] = mk[ToNatural] ℕ⁺.n
