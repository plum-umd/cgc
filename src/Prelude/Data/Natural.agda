module Prelude.Data.Natural where

open import Prelude.Core
open import Prelude.Relations
open import Prelude.Classes

----------------
-- Conversion --
----------------

record ToNatural {𝓁} (A : Set 𝓁) : Set 𝓁 where
  constructor mk[ToNatural]
  field
    𝕟 : A → ℕ
open ToNatural {{...}}

-------------
-- ≤ Order --
-------------

infix 8 _≤ⁿ_
data _≤ⁿ_ : ℕ → ℕ → Set where
  Zero : ∀ {n} → Zero ≤ⁿ n
  Suc : ∀ {n₁ n₂} → n₁ ≤ⁿ n₂ → Suc n₁ ≤ⁿ Suc n₂

_<ⁿ_ : relation zeroˡ ℕ
n₁ <ⁿ n₂ = Suc n₁ ≤ⁿ n₂

xRx⸢≤ⁿ⸣ : reflexive _≤ⁿ_
xRx⸢≤ⁿ⸣ {Zero} = Zero
xRx⸢≤ⁿ⸣ {Suc n} = Suc xRx⸢≤ⁿ⸣

_⌾⸢≤ⁿ⸣_ : transitive _≤ⁿ_
n₁≤n₂ ⌾⸢≤ⁿ⸣ Zero = Zero
Suc n₂≤n₃ ⌾⸢≤ⁿ⸣ Suc n₁≤n₂ = Suc (n₂≤n₃ ⌾⸢≤ⁿ⸣ n₁≤n₂)

⋈⸢≤ⁿ⸣ : antisymmetric _≤ⁿ_
⋈⸢≤ⁿ⸣ Zero Zero = ↯
⋈⸢≤ⁿ⸣ (Suc n₁≤n₂) (Suc n₂≤n₁) = res-x $ ⋈⸢≤ⁿ⸣ n₁≤n₂ n₂≤n₁

_⋚ⁿ_ : dec-total-order _≡_ _≤ⁿ_
Zero   ⋚ⁿ Zero   = [~] ↯
Zero   ⋚ⁿ Suc n₂ = [<] Zero (λ ())
Suc n₁ ⋚ⁿ Zero   = [>] Zero (λ ())
Suc n₁ ⋚ⁿ Suc n₂ with n₁ ⋚ⁿ n₂
... | [<] n₁≤n₂ not[n₂≤n₁] = [<] (Suc n₁≤n₂) BAD
  where
    BAD : Suc n₂ ≤ⁿ Suc n₁ → void
    BAD (Suc n₂≤n₁) = not[n₂≤n₁] n₂≤n₁
... | [~] n₁≡n₂ = [~] (res-x n₁≡n₂)
... | [>] n₁≥n₂ not[n₂≥n₁] = [>] (Suc n₁≥n₂) BAD
  where
    BAD : Suc n₁ ≤ⁿ Suc n₂ → void
    BAD (Suc n₂≥n₁) = not[n₂≥n₁] n₂≥n₁

weaken-suc-rhs⸢≤ⁿ⸣ : ∀ {n₁ n₂ : ℕ} → n₁ ≤ⁿ n₂ → n₁ ≤ⁿ Suc n₂
weaken-suc-rhs⸢≤ⁿ⸣ Zero = Zero
weaken-suc-rhs⸢≤ⁿ⸣ (Suc n₁≤n₂) = Suc (weaken-suc-rhs⸢≤ⁿ⸣ n₁≤n₂)

weaken-suc-lhs⸢≤ⁿ⸣ : ∀ {n₁ n₂ : ℕ} → Suc n₁ ≤ⁿ n₂ → n₁ ≤ⁿ n₂
weaken-suc-lhs⸢≤ⁿ⸣ (Suc n₁≤pred[n₂]) = weaken-suc-rhs⸢≤ⁿ⸣ n₁≤pred[n₂]

bad-xRx⸢≤ⁿ⸣ : ∀ {n : ℕ} → not (Suc n ≤ⁿ n)
bad-xRx⸢≤ⁿ⸣ {Zero} ()
bad-xRx⸢≤ⁿ⸣ {Suc n} (Suc n≤pred[n]) = bad-xRx⸢≤ⁿ⸣ n≤pred[n]

correct[<ⁿ] : ∀ {n₁ n₂} → n₁ <ⁿ n₂ ↔ n₁ ≤ⁿ n₂ × not (n₂ ≤ⁿ n₁)
correct[<ⁿ] = LHS , RHS
  where
    LHS : ∀ {n₁ n₂ : ℕ} → n₁ <ⁿ n₂ → n₁ ≤ⁿ n₂ × not (n₂ ≤ⁿ n₁)
    LHS (Suc n₁≤pred[n₂]) = weaken-suc-rhs⸢≤ⁿ⸣ n₁≤pred[n₂] , (λ n₁≤n₂ → bad-xRx⸢≤ⁿ⸣ (n₁≤pred[n₂] ⌾⸢≤ⁿ⸣ n₁≤n₂))
    RHS : ∀ {n₁ n₂ : ℕ} → n₁ ≤ⁿ n₂ × not (n₂ ≤ⁿ n₁) → n₁ <ⁿ n₂
    RHS {n₂ = Zero} (n₁≤n₂ , n₂≤/n₁) = exfalso $ n₂≤/n₁ Zero
    RHS {n₂ = Suc pred[n₂]} (Zero , n₂≤/n₁) = Suc Zero
    RHS {n₂ = Suc pred[n₂]} (Suc n₁≤n₂ , n₂≤/n₁) = Suc (RHS (n₁≤n₂ , (λ pred[n₂]≤n₁ → n₂≤/n₁ (Suc pred[n₂]≤n₁))))

xRsuc⸢≤ⁿ⸣ : ∀ {n : ℕ} → n ≤ⁿ Suc n
xRsuc⸢≤ⁿ⸣ = weaken-suc-rhs⸢≤ⁿ⸣ xRx⸢≤ⁿ⸣

instance
  Reflexive[≤ⁿ] : Reflexive _≤ⁿ_
  Reflexive[≤ⁿ] = record { xRx = xRx⸢≤ⁿ⸣ }
  Transitive[≤ⁿ] : Transitive _≤ⁿ_
  Transitive[≤ⁿ] = record { _⌾_ = _⌾⸢≤ⁿ⸣_ }
  Antisymmetric[≤ⁿ] : Antisymmetric _≤ⁿ_
  Antisymmetric[≤ⁿ] = record { ⋈ = ⋈⸢≤ⁿ⸣ }
  TotalOrder[≤ⁿ] : TotalOrder zeroˡ ℕ
  TotalOrder[≤ⁿ] = record
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
weaken-ℕ≤ nᵇ₁≤nᵇ₂ (mk[ℕ≤] n n≤nᵇ₁) = mk[ℕ≤] n (nᵇ₁≤nᵇ₂ ⌾ n≤nᵇ₁)

instance
  ToNatural[ℕ≤] : ∀ {nᵇ} → ToNatural ℕ≤[ nᵇ ]
  ToNatural[ℕ≤] = mk[ToNatural] ℕ≤[_].n

record ℕ<[_] (nᵇ : ℕ) : Set where
  constructor mk[ℕ<]
  field
    n : ℕ
    n<nᵇ : n < nᵇ
    
mk[ℕ<]⸢↯⸣ : ∀ {nᵇ} n → {{IY : is-rel (dec[≤ⁿ] (Suc n) nᵇ)}} → ℕ<[ nᵇ ]
mk[ℕ<]⸢↯⸣ {nᵇ} n {{IY}} with dec[≤ⁿ] (Suc n) nᵇ
mk[ℕ<]⸢↯⸣ {nᵇ} n {{↯Rel}} | Yes n<nᵇ = mk[ℕ<] n n<nᵇ

weaken-ℕ< : ∀ {nᵇ₁ nᵇ₂} → nᵇ₁ ≤ nᵇ₂ → ℕ<[ nᵇ₁ ] → ℕ<[ nᵇ₂ ]
weaken-ℕ< nᵇ₁≤nᵇ₂ (mk[ℕ<] n n<nᵇ₁) = mk[ℕ<] n (nᵇ₁≤nᵇ₂ ⌾ n<nᵇ₁)

instance
  ToNatural[ℕ<] : ∀ {nᵇ} → ToNatural ℕ<[ nᵇ ]
  ToNatural[ℕ<] = mk[ToNatural] ℕ<[_].n

data fin : ℕ → Set where
  Zero : ∀ {n} → fin (Suc n)
  Suc : ∀ {n} → fin n → fin (Suc n)

fin⸢<ⁿ⸣ : ∀ {nᵇ} n → n <ⁿ nᵇ → fin nᵇ
fin⸢<ⁿ⸣ Zero (Suc n<nᵇ) = Zero
fin⸢<ⁿ⸣ (Suc n) (Suc n<nᵇ) = Suc (fin⸢<ⁿ⸣ n n<nᵇ)

fin⸢ℕ<⸣ : ∀ {nᵇ} → ℕ<[ nᵇ ] → fin nᵇ
fin⸢ℕ<⸣ (mk[ℕ<] n n<nᵇ) = fin⸢<ⁿ⸣ n n<nᵇ

record ℕ⁺ : Set where
  constructor mk[ℕ⁺]
  field
    n : ℕ
    0<n : 0 < n

mk[ℕ⁺]⸢↯⸣ : ∀ n {{IY : is-rel (dec[≤ⁿ] (Suc 0) n)}} → ℕ⁺
mk[ℕ⁺]⸢↯⸣ n {{IY}} with dec[≤ⁿ] (Suc 0) n
mk[ℕ⁺]⸢↯⸣ n {{↯Rel}} | Yes 0<n = mk[ℕ⁺] n 0<n

instance
  ToNatural[ℕ⁺] : ToNatural ℕ⁺
  ToNatural[ℕ⁺] = mk[ToNatural] ℕ⁺.n

--------------
-- Addition --
--------------

infixr 5 _+ⁿ_
_+ⁿ_ : ℕ → ℕ → ℕ
Zero +ⁿ n₂ = n₂
Suc n₁ +ⁿ n₂ = Suc (n₁ +ⁿ n₂)

left-unit[+ⁿ] : ∀ (n : ℕ) → 0 +ⁿ n ≡ n
left-unit[+ⁿ] n = ↯

right-unit[+ⁿ] : ∀ (n : ℕ) → n +ⁿ 0 ≡ n
right-unit[+ⁿ] Zero = ↯
right-unit[+ⁿ] (Suc n) rewrite right-unit[+ⁿ] n = ↯

associative[+ⁿ] : ∀ (n₁ n₂ n₃ : ℕ) → (n₁ +ⁿ n₂) +ⁿ n₃ ≡ n₁ +ⁿ n₂ +ⁿ n₃
associative[+ⁿ] Zero n₂ n₃ = ↯
associative[+ⁿ] (Suc n₁) n₂ n₃ rewrite associative[+ⁿ] n₁ n₂ n₃ = ↯

m+suc[n]=suc[m+n] : ∀ (n₁ n₂ : ℕ) → n₁ +ⁿ Suc n₂ ≡ Suc (n₁ +ⁿ n₂)
m+suc[n]=suc[m+n] Zero n₂ = ↯
m+suc[n]=suc[m+n] (Suc n₁) n₂ rewrite m+suc[n]=suc[m+n] n₁ n₂ = ↯

suc[m+n]=m+suc[n] : ∀ (n₁ n₂ : ℕ) → Suc (n₁ +ⁿ n₂) ≡ n₁ +ⁿ Suc n₂
suc[m+n]=m+suc[n] n₁ n₂ = ◇ $ m+suc[n]=suc[m+n] n₁ n₂

commutative[+ⁿ] : ∀ (n₁ n₂ : ℕ) → n₁ +ⁿ n₂ ≡ n₂ +ⁿ n₁
commutative[+ⁿ] Zero n₂ rewrite right-unit[+ⁿ] n₂ = ↯
commutative[+ⁿ] (Suc n₁) n₂ rewrite commutative[+ⁿ] n₁ n₂ | suc[m+n]=m+suc[n] n₂ n₁ = ↯

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
oneⁿ = Suc Zero

_⨯ⁿ_ : ℕ → ℕ → ℕ
Zero ⨯ⁿ n₂ = Zero
Suc n₁ ⨯ⁿ n₂ = n₂ +ⁿ n₁ ⨯ⁿ n₂

left-zero[⨯ⁿ] : ∀ n → zero ⨯ⁿ n ≡ zero
left-zero[⨯ⁿ] n = ↯

right-zero[⨯ⁿ] : ∀ n → n ⨯ⁿ zero ≡ zero
right-zero[⨯ⁿ] Zero = ↯
right-zero[⨯ⁿ] (Suc n) rewrite right-zero[⨯ⁿ] n = ↯

left-unit[⨯ⁿ] : ∀ n → oneⁿ ⨯ⁿ n ≡ n
left-unit[⨯ⁿ] n = right-unit[+ⁿ] n

right-unit[⨯ⁿ] : ∀ n → n ⨯ⁿ oneⁿ ≡ n
right-unit[⨯ⁿ] Zero = ↯
right-unit[⨯ⁿ] (Suc n) rewrite right-unit[⨯ⁿ] n = ↯

distributive[⨯ⁿ] : ∀ n₁ n₂ n₃ → (n₁ +ⁿ n₂) ⨯ⁿ n₃ ≡ n₁ ⨯ⁿ n₃ +ⁿ n₂ ⨯ⁿ n₃
distributive[⨯ⁿ] Zero n₂ n₃ = ↯
distributive[⨯ⁿ] (Suc n₁) n₂ n₃ rewrite distributive[⨯ⁿ] n₁ n₂ n₃ | associative[+ⁿ] n₃ (n₁ ⨯ⁿ n₃) (n₂ ⨯ⁿ n₃) = ↯

associative[⨯ⁿ] : ∀ n₁ n₂ n₃ → (n₁ ⨯ⁿ n₂) ⨯ⁿ n₃ ≡ n₁ ⨯ⁿ (n₂ ⨯ⁿ n₃)
associative[⨯ⁿ] Zero n₂ n₃ = ↯
associative[⨯ⁿ] (Suc n₁) n₂ n₃ rewrite distributive[⨯ⁿ] n₂ (n₁ ⨯ⁿ n₂) n₃ | associative[⨯ⁿ] n₁ n₂ n₃ = ↯

commutative[⨯ⁿ] : ∀ n₁ n₂ → n₁ ⨯ⁿ n₂ ≡ n₂ ⨯ⁿ n₁
commutative[⨯ⁿ] Zero n₂ rewrite right-zero[⨯ⁿ] n₂ = ↯
commutative[⨯ⁿ] n₁ Zero rewrite right-zero[⨯ⁿ] n₁ = ↯
commutative[⨯ⁿ] (Suc n₁) (Suc n₂)
  rewrite commutative[⨯ⁿ] n₁ (Suc n₂)
        | commutative[⨯ⁿ] n₂ (Suc n₁)
        | commutative[⨯ⁿ] n₁ n₂
        | ◇ $ associative[+ⁿ] n₁ n₂ (n₂ ⨯ⁿ n₁)
        | commutative[+ⁿ] n₁ n₂
        | associative[+ⁿ] n₂ n₁ (n₂ ⨯ⁿ n₁)
        = ↯

instance
  Multiplicative[ℕ] : Multiplicative ℕ
  Multiplicative[ℕ] = record
    { one = oneⁿ
    ; _⨯_ = _⨯ⁿ_
    ; left-zero[⨯] = left-zero[⨯ⁿ]
    ; right-zero[⨯] = right-zero[⨯ⁿ]
    ; left-unit[⨯] = left-unit[⨯ⁿ]
    ; right-unit[⨯] = right-unit[⨯ⁿ]
    ; associative[⨯] = associative[⨯ⁿ]
    ; commutative[⨯] = commutative[⨯ⁿ]
    ; distributive[⨯] = distributive[⨯ⁿ]
    }

-----------------
-- Subtraction --
-----------------

_-ⁿ_‖_ : ∀ (n₁ n₂ : ℕ) → n₂ ≤ⁿ n₁ → ℕ
n₁ -ⁿ Zero ‖ Zero = n₁
Suc n₁ -ⁿ Suc n₂ ‖ Suc n₁≤n₂ = n₁ -ⁿ n₂ ‖ n₁≤n₂

correct[-ⁿ‖] : ∀ n₁ n₂ (n₂≤n₁ : n₂ ≤ n₁) → n₂ + (n₁ -ⁿ n₂ ‖ n₂≤n₁) ≡ n₁
correct[-ⁿ‖] n₁ Zero Zero = ↯
correct[-ⁿ‖] (Suc n₁) (Suc n₂) (Suc n₂≤n₁) rewrite correct[-ⁿ‖] n₁ n₂ n₂≤n₁ = ↯

n-n=0 : ∀ n → n -ⁿ n ‖ xRx ≡ Zero
n-n=0 Zero = ↯
n-n=0 (Suc n) rewrite n-n=0 n = ↯

n-0=n : ∀ n → n -ⁿ 0 ‖ Zero ≡ n
n-0=n n = ↯

suc[m-n]=suc[m]-n : ∀ n₁ n₂ (n₂≤n₁ : n₂ ≤ n₁) → Suc (n₁ -ⁿ n₂ ‖ n₂≤n₁) ≡ Suc n₁ -ⁿ n₂ ‖ weaken-suc-rhs⸢≤ⁿ⸣ n₂≤n₁
suc[m-n]=suc[m]-n n₁ Zero Zero = ↯
suc[m-n]=suc[m]-n (Suc n₁) (Suc n₂) (Suc n₂≤n₁) rewrite suc[m-n]=suc[m]-n n₁ n₂ n₂≤n₁ = ↯

instance
  Subtractive[ℕ] : Subtractiveᵖ ℕ _≥_
  Subtractive[ℕ] = record
    { ok[x-x] = λ x → xRx
    ; _-_‖_ = _-ⁿ_‖_
    ; correct[-‖] = correct[-ⁿ‖]
    }

--------------------------
-- Division and Modulus --
--------------------------

divmod-loop : ∀ (n₁ n₂ quo n₂-rem : ℕ) → n₂-rem ≤ n₂ → ∃ quo,n₂-rem ⦂ ℕ × ℕ 𝑠𝑡 let quo' , n₂-rem' = quo,n₂-rem in n₂-rem' ≤ n₂
divmod-loop Zero n₂ quo n₂-rem n₂-rem≤n₂ = ∃ quo , n₂-rem ,, n₂-rem≤n₂
divmod-loop (Suc n₁) n₂ quo Zero n₂-rem≤n₂ = divmod-loop n₁ n₂ (Suc quo) n₂ xRx
divmod-loop (Suc n₁) n₂ quo (Suc n₂-rem) n₂-rem≤n₂ = divmod-loop n₁ n₂ quo n₂-rem (weaken-suc-lhs⸢≤ⁿ⸣ n₂-rem≤n₂)

correct[divmod-loop] :
  ∀ (n₁ n₂ quo n₂-rem : ℕ) (n₂-rem≤n₂ : n₂-rem ≤ n₂)
  → let ∃ quo' , n₂-rem' ,, n₂-rem'≤n₂ = divmod-loop n₁ n₂ quo n₂-rem n₂-rem≤n₂ in 
    quo' ⨯ Suc n₂ + (n₂ - n₂-rem' ‖ n₂-rem'≤n₂) ≡ n₁ + (quo ⨯ Suc n₂) + (n₂ - n₂-rem ‖ n₂-rem≤n₂)
correct[divmod-loop] Zero n₂ quo n₂-rem n₂-rem≤n₂ = ↯
correct[divmod-loop] (Suc n₁) n₂ quo Zero Zero
  with divmod-loop n₁ n₂ (Suc quo) n₂ xRx⸢≤ⁿ⸣
     | correct[divmod-loop] n₁ n₂ (Suc quo) n₂ xRx⸢≤ⁿ⸣
... | ∃ quo' , n₂-rem' ,, n₂-rem'≤n₂ | IH
  rewrite suc[m+n]=m+suc[n] n₁ (quo ⨯ⁿ Suc n₂ +ⁿ n₂ -ⁿ 0 ‖ Zero)
        | n-n=0 n₂
        | commutative[+ⁿ] (quo ⨯ⁿ Suc n₂) n₂
        | right-unit[+ⁿ] (n₂ +ⁿ quo ⨯ⁿ Suc n₂)
        = IH
correct[divmod-loop] (Suc n₁) (Suc n₂) quo (Suc n₂-rem) (Suc n₂-rem≤n₂)
  with divmod-loop n₁ (Suc n₂) quo n₂-rem (weaken-suc-rhs⸢≤ⁿ⸣ n₂-rem≤n₂)
     | correct[divmod-loop] n₁ (Suc n₂) quo n₂-rem (weaken-suc-rhs⸢≤ⁿ⸣ n₂-rem≤n₂)
... | ∃ quo' , n₂-rem' ,, n₂-rem'≤n₂ | IH 
  rewrite suc[m+n]=m+suc[n] n₁ (quo ⨯ⁿ Suc (Suc n₂) +ⁿ n₂ -ⁿ n₂-rem ‖ n₂-rem≤n₂)
        | suc[m+n]=m+suc[n] (quo ⨯ⁿ Suc (Suc n₂)) (n₂ -ⁿ n₂-rem ‖ n₂-rem≤n₂)
        | suc[m-n]=suc[m]-n n₂ n₂-rem n₂-rem≤n₂
        = IH

_/%ⁿ_‖_ : ∀ (n₁ n₂ : ℕ) (0<n₂ : 0 < n₂) → ℕ × ℕ
n₁ /%ⁿ Suc n₂ ‖ Suc 0<n₂ with divmod-loop n₁ n₂ 0 n₂ xRx⸢≤ⁿ⸣
... | ∃ quo , n₂-rem ,, n₂-rem≤n₂ = quo , n₂ - n₂-rem ‖ n₂-rem≤n₂

correct[/%‖ⁿ] : ∀ n₁ n₂ (0<n₂ : 0 < n₂) → let quo , rem = n₁ /%ⁿ n₂ ‖ 0<n₂ in n₂ ⨯ quo + rem ≡ n₁
correct[/%‖ⁿ] n₁ (Suc n₂) (Suc 0<n₂) with divmod-loop n₁ n₂ 0 n₂ xRx | correct[divmod-loop] n₁ n₂ 0 n₂ xRx
... | ∃ quo , n₂-rem ,, n₂-rem≤n₂ | H rewrite n-n=0 n₂ | right-unit[+ⁿ] n₁ | commutative[⨯ⁿ] quo (Suc n₂) = H

instance
  DivMod[ℕ] : DivModᵖ ℕ (λ n₁ n₂ → 0 < n₂)
  DivMod[ℕ] = record
    { _/%_‖_ = _/%ⁿ_‖_
    ; correct[/%‖] = correct[/%‖ⁿ]
    }
