module Prelude.Data.Natural where

open import Prelude.Core
open import Prelude.Classes
open import Prelude.Orders

----------------
-- Conversion --
----------------

record ToNatural {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mk[ToNatural]
  field
    𝕟 : A → ℕ
open ToNatural {{…}}

-----------
-- Order --
-----------

data _≤ⁿ_ : ℕ → ℕ → Set where
  Zero : ∀ {n} → Zero ≤ⁿ n
  Succ : ∀ {n₁ n₂} → n₁ ≤ⁿ n₂ → Succ n₁ ≤ⁿ Succ n₂

xRx⸢≤ⁿ⸣ : reflexive _≤ⁿ_
xRx⸢≤ⁿ⸣ {Zero} = Zero
xRx⸢≤ⁿ⸣ {Succ n} = Succ xRx⸢≤ⁿ⸣

⋈⸢≤ⁿ⸣ : antisymmetric _≤ⁿ_
⋈⸢≤ⁿ⸣ Zero Zero = ↯
⋈⸢≤ⁿ⸣ (Succ n₁≤n₂) (Succ n₂≤n₁) = res[•x] $ ⋈⸢≤ⁿ⸣ n₁≤n₂ n₂≤n₁

_⊚⸢≤ⁿ⸣_ : transitive _≤ⁿ_
n₁≤n₂ ⊚⸢≤ⁿ⸣ Zero = Zero
Succ n₂≤n₃ ⊚⸢≤ⁿ⸣ Succ n₁≤n₂ = Succ (n₂≤n₃ ⊚⸢≤ⁿ⸣ n₁≤n₂)

data _<ⁿ_ : ℕ → ℕ → Set where
  Zero : ∀ {n} → Zero <ⁿ Succ n
  Succ : ∀ {n₁ n₂} → n₁ <ⁿ n₂ → Succ n₁ <ⁿ Succ n₂

weaken[<]ⁿ : ∀ {n₁ n₂} → n₁ <ⁿ n₂ → n₁ ≤ⁿ n₂
weaken[<]ⁿ Zero = Zero
weaken[<]ⁿ (Succ <₁) = Succ (weaken[<]ⁿ <₁)

strict[<]ⁿ : ∀ {n₁ n₂} → n₁ <ⁿ n₂ → ¬ (n₂ ≤ⁿ n₁)
strict[<]ⁿ Zero ()
strict[<]ⁿ (Succ <₁) (Succ ≤₁) = strict[<]ⁿ <₁ ≤₁

complete[<]ⁿ : ∀ {n₁ n₂} → n₁ ≤ⁿ n₂ → ¬ (n₂ ≤ⁿ n₁) → n₁ <ⁿ n₂
complete[<]ⁿ {n₂ = Zero} Zero ¬≤ = exfalso (¬≤ Zero)
complete[<]ⁿ {n₂ = Succ n₂} Zero ¬≤ = Zero
complete[<]ⁿ (Succ ≤₁) ¬≤ = Succ (complete[<]ⁿ ≤₁ (λ ≤₂ → ¬≤ (Succ ≤₂)))

_⋚ⁿ_ : ℕ → ℕ → ⪥!
Zero ⋚ⁿ Zero = [≡]
Zero ⋚ⁿ Succ n₂ = [<]
Succ n₁ ⋚ⁿ Zero = [>]
Succ n₁ ⋚ⁿ Succ n₂ = n₁ ⋚ⁿ n₂

_⋚ⁿᴾ_ : ∀ n₁ n₂ → n₁ ⪥!ᴾ[ _<ⁿ_ ] n₂
Zero ⋚ⁿᴾ Zero = [≡] ↯
Zero ⋚ⁿᴾ Succ n₂ = [<] Zero
Succ n₁ ⋚ⁿᴾ Zero = [>] Zero
Succ n₁ ⋚ⁿᴾ Succ n₂ with n₁ ⋚ⁿᴾ n₂
… | [<] <₀ = [<] (Succ <₀)
… | [≡] ≡₀ rewrite ≡₀ = [≡] ↯
… | [>] >₀ = [>] (Succ >₀)

_⋚ⁿᴸ_ : ∀ n₁ n₂ → n₁ ⪥!ᴸ[ _<ⁿ_ ] n₂ ‖[ n₁ ⋚ⁿ n₂ , n₁ ⋚ⁿᴾ n₂ ]
Zero ⋚ⁿᴸ Zero = [≡]
Zero ⋚ⁿᴸ Succ n₂ = [<]
Succ n₁ ⋚ⁿᴸ Zero = [>]
Succ n₁ ⋚ⁿᴸ Succ n₂ with n₁ ⋚ⁿ n₂ | n₁ ⋚ⁿᴾ n₂ | n₁ ⋚ⁿᴸ n₂
… | [<] | [<] <₀ | [<] = [<]
… | [≡] | [≡] ≡₀ | [≡] rewrite ≡₀ = [≡]
… | [>] | [>] >₀ | [>] = [>]

instance
  Reflexive[≤]ⁿ : Reflexive _≤ⁿ_
  Reflexive[≤]ⁿ = record { xRx = xRx⸢≤ⁿ⸣ }
  Antisymmetric[≤]ⁿ : Antisymmetric _≤ⁿ_
  Antisymmetric[≤]ⁿ = record { ⋈ = ⋈⸢≤ⁿ⸣ }
  Transitive[≤]ⁿ : Transitive _≤ⁿ_
  Transitive[≤]ⁿ = record { _⊚_ = _⊚⸢≤ⁿ⸣_ }
  Strict[<]ⁿ : Strict _≤ⁿ_ _<ⁿ_
  Strict[<]ⁿ = record
    { weaken[≺] = weaken[<]ⁿ
    ; strict[≺] = strict[<]ⁿ
    ; complete[≺] = complete[<]ⁿ
    }
  Irreflexive[<]ⁿ : Irreflexive _<ⁿ_
  Irreflexive[<]ⁿ = Irreflexive[<]/≤ _≤ⁿ_ _<ⁿ_
  Asymmetric[<]ⁿ : Asymmetric _<ⁿ_
  Asymmetric[<]ⁿ = Asymmetric[<]/≤ _≤ⁿ_ _<ⁿ_
  Transitive[<]ⁿ : Transitive _<ⁿ_
  Transitive[<]ⁿ = Transitive[<]/≤ _≤ⁿ_ _<ⁿ_
  Totally[<]ⁿ : Totally _<ⁿ_
  Totally[<]ⁿ = record
    { _⪥_ = _⋚ⁿ_
    ; _⪥ᴾ_ = _⋚ⁿᴾ_
    ; _⪥ᴸ_ = _⋚ⁿᴸ_
    }
  Order[ℕ] : Order 0ᴸ ℕ
  Order[ℕ] = mk[Order] _≤ⁿ_ _<ⁿ_

weaken[≤]ⁿ : ∀ {n₁ n₂} → n₁ ≤ⁿ n₂ → n₁ ≤ⁿ Succ n₂
weaken[≤]ⁿ Zero = Zero
weaken[≤]ⁿ (Succ n₁≤n₂) = Succ (weaken[≤]ⁿ n₁≤n₂)

pred[≤]ⁿ : ∀ {n₁ n₂} → Succ n₁ ≤ⁿ n₂ → n₁ ≤ⁿ n₂
pred[≤]ⁿ (Succ x) = weaken[≤]ⁿ x

n≤succ : ∀ {n : ℕ} → n ≤ⁿ Succ n
n≤succ = weaken[≤]ⁿ xRx

rel[</≤]ⁿ : ∀ {n₁ n₂} → n₁ <ⁿ n₂ ↔ Succ n₁ ≤ⁿ n₂
rel[</≤]ⁿ = ⟨ LHS , RHS ⟩
  where
    LHS : ∀ {n₁ n₂} → n₁ <ⁿ n₂ → Succ n₁ ≤ⁿ n₂
    LHS Zero = Succ Zero
    LHS (Succ <₁) = Succ (LHS <₁)
    RHS : ∀ {n₁ n₂} → Succ n₁ ≤ⁿ n₂ → n₁ <ⁿ n₂
    RHS {Zero} (Succ ≤₁) = Zero
    RHS {Succ n₃} (Succ ≤₁) = Succ (RHS ≤₁)


------------------
-- ≤ⁿ Decidable --
------------------

instance
  DecRel[≡]ⁿ : DecRel (_≡_ {A = ℕ})
  DecRel[≡]ⁿ = record
    { _⁇_ = ⁇[≡]/⪥[] _≤_ _<_
    ; _⁇ᴾ_ = ⁇ᴾ[≡]/⪥[] _≤_ _<_
    ; _⁇ᴸ_ = ⁇ᴸ[≡]/⪥[] _≤_ _<_
    }
  DecRel[≤]ⁿ : DecRel _≤ⁿ_
  DecRel[≤]ⁿ = record
    { _⁇_ = ⁇[≤]/⪥[] _≤_ _<_
    ; _⁇ᴾ_ = ⁇ᴾ[≤]/⪥[] _≤_ _<_
    ; _⁇ᴸ_ = ⁇ᴸ[≤]/⪥[] _≤_ _<_
    }
  DecRel[<]ⁿ : DecRel _<ⁿ_
  DecRel[<]ⁿ = record
    { _⁇_ = ⁇[<]/⪥[] _≤_ _<_
    ; _⁇ᴾ_ = ⁇ᴾ[<]/⪥[] _≤_ _<_
    ; _⁇ᴸ_ = ⁇ᴸ[<]/⪥[] _≤_ _<_
    }

--------------
-- Addition --
--------------

_+ⁿ_ : ℕ → ℕ → ℕ
Zero +ⁿ n₂ = n₂
Succ n₁ +ⁿ n₂ = Succ (n₁ +ⁿ n₂)

left-unit[+]ⁿ : ∀ (n : ℕ) → 0 +ⁿ n ≡ n
left-unit[+]ⁿ n = ↯

right-unit[+]ⁿ : ∀ (n : ℕ) → n +ⁿ 0 ≡ n
right-unit[+]ⁿ Zero = ↯
right-unit[+]ⁿ (Succ n) rewrite right-unit[+]ⁿ n = ↯

associative[+]ⁿ : ∀ (n₁ n₂ n₃ : ℕ) → (n₁ +ⁿ n₂) +ⁿ n₃ ≡ n₁ +ⁿ (n₂ +ⁿ n₃)
associative[+]ⁿ Zero n₂ n₃ = ↯
associative[+]ⁿ (Succ n₁) n₂ n₃ rewrite associative[+]ⁿ n₁ n₂ n₃ = ↯

m+suc[n]=suc[m+n] : ∀ (n₁ n₂ : ℕ) → n₁ +ⁿ Succ n₂ ≡ Succ (n₁ +ⁿ n₂)
m+suc[n]=suc[m+n] Zero n₂ = ↯
m+suc[n]=suc[m+n] (Succ n₁) n₂ rewrite m+suc[n]=suc[m+n] n₁ n₂ = ↯

suc[m+n]=m+suc[n] : ∀ (n₁ n₂ : ℕ) → Succ (n₁ +ⁿ n₂) ≡ n₁ +ⁿ Succ n₂
suc[m+n]=m+suc[n] n₁ n₂ = ◇ $ m+suc[n]=suc[m+n] n₁ n₂

commutative[+]ⁿ : ∀ (n₁ n₂ : ℕ) → n₁ +ⁿ n₂ ≡ n₂ +ⁿ n₁
commutative[+]ⁿ Zero n₂ rewrite right-unit[+]ⁿ n₂ = ↯
commutative[+]ⁿ (Succ n₁) n₂ rewrite commutative[+]ⁿ n₁ n₂ | suc[m+n]=m+suc[n] n₂ n₁ = ↯

instance
  Additive[ℕ] : Additive ℕ
  Additive[ℕ] = record
    { zero = Zero
    ; _+_ = _+ⁿ_
    ; left-unit[+] = left-unit[+]ⁿ
    ; right-unit[+] = right-unit[+]ⁿ
    ; associative[+] = associative[+]ⁿ
    ; commutative[+] = commutative[+]ⁿ
    }

--------------------
-- Multiplication --
--------------------

oneⁿ : ℕ
oneⁿ = Succ Zero

_×ⁿ_ : ℕ → ℕ → ℕ
Zero ×ⁿ n₂ = Zero
Succ n₁ ×ⁿ n₂ = n₂ +ⁿ (n₁ ×ⁿ n₂)

left-zero[×]ⁿ : ∀ n → zero ×ⁿ n ≡ zero
left-zero[×]ⁿ n = ↯

right-zero[×]ⁿ : ∀ n → n ×ⁿ zero ≡ zero
right-zero[×]ⁿ Zero = ↯
right-zero[×]ⁿ (Succ n) rewrite right-zero[×]ⁿ n = ↯

left-unit[×]ⁿ : ∀ n → oneⁿ ×ⁿ n ≡ n
left-unit[×]ⁿ n = right-unit[+]ⁿ n

right-unit[×]ⁿ : ∀ n → n ×ⁿ oneⁿ ≡ n
right-unit[×]ⁿ Zero = ↯
right-unit[×]ⁿ (Succ n) rewrite right-unit[×]ⁿ n = ↯

distributive[×]ⁿ : ∀ n₁ n₂ n₃ → (n₁ +ⁿ n₂) ×ⁿ n₃ ≡ (n₁ ×ⁿ n₃) +ⁿ (n₂ ×ⁿ n₃)
distributive[×]ⁿ Zero n₂ n₃ = ↯
distributive[×]ⁿ (Succ n₁) n₂ n₃ rewrite distributive[×]ⁿ n₁ n₂ n₃ | associative[+]ⁿ n₃ (n₁ ×ⁿ n₃) (n₂ ×ⁿ n₃) = ↯

associative[×]ⁿ : ∀ n₁ n₂ n₃ → (n₁ ×ⁿ n₂) ×ⁿ n₃ ≡ n₁ ×ⁿ (n₂ ×ⁿ n₃)
associative[×]ⁿ Zero n₂ n₃ = ↯
associative[×]ⁿ (Succ n₁) n₂ n₃ rewrite distributive[×]ⁿ n₂ (n₁ ×ⁿ n₂) n₃ | associative[×]ⁿ n₁ n₂ n₃ = ↯

commutative[×]ⁿ : ∀ n₁ n₂ → n₁ ×ⁿ n₂ ≡ n₂ ×ⁿ n₁
commutative[×]ⁿ Zero n₂ rewrite right-zero[×]ⁿ n₂ = ↯
commutative[×]ⁿ n₁ Zero rewrite right-zero[×]ⁿ n₁ = ↯
commutative[×]ⁿ (Succ n₁) (Succ n₂)
  rewrite commutative[×]ⁿ n₁ (Succ n₂)
        | commutative[×]ⁿ n₂ (Succ n₁)
        | commutative[×]ⁿ n₁ n₂
        | ◇ $ associative[+]ⁿ n₁ n₂ (n₂ ×ⁿ n₁)
        | commutative[+]ⁿ n₁ n₂
        | associative[+]ⁿ n₂ n₁ (n₂ ×ⁿ n₁)
        = ↯

instance
  Multiplicative[ℕ] : Multiplicative ℕ
  Multiplicative[ℕ] = record
    { one = oneⁿ
    ; _×_ = _×ⁿ_
    ; left-zero[×] = left-zero[×]ⁿ
    ; right-zero[×] = right-zero[×]ⁿ
    ; left-unit[×] = left-unit[×]ⁿ
    ; right-unit[×] = right-unit[×]ⁿ
    ; associative[×] = associative[×]ⁿ
    ; commutative[×] = commutative[×]ⁿ
    ; distributive[×] = distributive[×]ⁿ
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

suc[m-n]=suc[m]-n : ∀ n₁ n₂ (n₂≤n₁ : n₂ ≤ n₁) → Succ (n₁ -ⁿ n₂ ‖ n₂≤n₁) ≡ Succ n₁ -ⁿ n₂ ‖ weaken[≤]ⁿ n₂≤n₁
suc[m-n]=suc[m]-n n₁ Zero Zero = ↯
suc[m-n]=suc[m]-n (Succ n₁) (Succ n₂) (Succ n₂≤n₁) rewrite suc[m-n]=suc[m]-n n₁ n₂ n₂≤n₁ = ↯

instance
  Subtractive/OK[ℕ] : Subtractive/OK ℕ
  Subtractive/OK[ℕ] = record { ok[_-_] = _≥_ }
  Subtractive[ℕ] : Subtractive/P ℕ
  Subtractive[ℕ] = record
    { _-_‖_ = _-ⁿ_‖_
    ; correct[-‖] = correct[-ⁿ‖]
    }

_-%ⁿ_ : ∀ (n₁ n₂ : ℕ) → ℕ ∨ ℕ
Zero -%ⁿ n₂ = Inr n₂
n₁ -%ⁿ Zero = Inl n₁
Succ n₁ -%ⁿ Succ n₂ = n₁ -%ⁿ n₂

correct[-%ⁿ]/spec : ℕ → ℕ → Set
correct[-%ⁿ]/spec n₁ n₂ with n₁ -%ⁿ n₂
… | Inl n = n₂ + n ≡ n₁
… | Inr n = n₁ + n ≡ n₂

correct[-%ⁿ] : ∀ n₁ n₂ → correct[-%ⁿ]/spec n₁ n₂
correct[-%ⁿ] Zero Zero = ↯
correct[-%ⁿ] Zero (Succ n₂) = ↯
correct[-%ⁿ] (Succ n₁) Zero = ↯
correct[-%ⁿ] (Succ n₁) (Succ n₂) with n₁ -%ⁿ n₂ | correct[-%ⁿ] n₁ n₂
… | Inl x | IH rewrite IH = ↯
… | Inr x | IH rewrite IH = ↯

--------------------------
-- Division and Modulus --
--------------------------

divmod-loop : ∀ (n₁ n₂ quo n₂-rem : ℕ) → n₂-rem ≤ n₂ → ∃ quo,n₂-rem ⦂ ℕ ∧ ℕ 𝑠𝑡 let ⟨ quo' , n₂-rem' ⟩ = quo,n₂-rem in n₂-rem' ≤ n₂
divmod-loop Zero n₂ quo n₂-rem n₂-rem≤n₂ = ⟨∃ ⟨ quo , n₂-rem ⟩ , n₂-rem≤n₂ ⟩
divmod-loop (Succ n₁) n₂ quo Zero n₂-rem≤n₂ = divmod-loop n₁ n₂ (Succ quo) n₂ xRx
divmod-loop (Succ n₁) n₂ quo (Succ n₂-rem) n₂-rem≤n₂ = divmod-loop n₁ n₂ quo n₂-rem (pred[≤]ⁿ n₂-rem≤n₂)

correct[divmod-loop] :
  ∀ (n₁ n₂ quo n₂-rem : ℕ) (n₂-rem≤n₂ : n₂-rem ≤ n₂)
  → let ⟨∃ ⟨ quo' , n₂-rem' ⟩ , n₂-rem'≤n₂ ⟩ = divmod-loop n₁ n₂ quo n₂-rem n₂-rem≤n₂ in 
    quo' × Succ n₂ + (n₂ - n₂-rem' ‖ n₂-rem'≤n₂) ≡ n₁ + (quo × Succ n₂) + (n₂ - n₂-rem ‖ n₂-rem≤n₂)
correct[divmod-loop] Zero n₂ quo n₂-rem n₂-rem≤n₂ = ↯
correct[divmod-loop] (Succ n₁) n₂ quo Zero Zero
  with divmod-loop n₁ n₂ (Succ quo) n₂ xRx
     | correct[divmod-loop] n₁ n₂ (Succ quo) n₂ xRx
… | ⟨∃ ⟨ quo' , n₂-rem' ⟩ , n₂-rem'≤n₂ ⟩ | IH
  rewrite suc[m+n]=m+suc[n] n₁ (quo × Succ n₂ + n₂ - Zero ‖ Zero)
        | n-n=0 n₂
        | commutative[+] (quo × Succ n₂) n₂
        | right-unit[+] (n₂ + quo × Succ n₂)
        = IH
correct[divmod-loop] (Succ n₁) (Succ n₂) quo (Succ n₂-rem) (Succ n₂-rem≤n₂)
  with divmod-loop n₁ (Succ n₂) quo n₂-rem (weaken[≤]ⁿ n₂-rem≤n₂)
     | correct[divmod-loop] n₁ (Succ n₂) quo n₂-rem (weaken[≤]ⁿ n₂-rem≤n₂)
… | ⟨∃ ⟨ quo' , n₂-rem' ⟩ , n₂-rem'≤n₂ ⟩ | IH 
  rewrite suc[m+n]=m+suc[n] n₁ (quo × Succ (Succ n₂) + n₂ - n₂-rem ‖ n₂-rem≤n₂)
        | suc[m+n]=m+suc[n] (quo × Succ (Succ n₂)) (n₂ - n₂-rem ‖ n₂-rem≤n₂)
        | suc[m-n]=suc[m]-n n₂ n₂-rem n₂-rem≤n₂
        = IH

_/%ⁿ_‖_ : ∀ (n₁ n₂ : ℕ) (0<n₂ : 0 < n₂) → ℕ ∧ ℕ
n₁ /%ⁿ Succ n₂ ‖ Zero with divmod-loop n₁ n₂ 0 n₂ xRx⸢≤ⁿ⸣
… | ⟨∃ ⟨ quo , n₂-rem ⟩ , n₂-rem≤n₂ ⟩ = ⟨ quo , n₂ - n₂-rem ‖ n₂-rem≤n₂ ⟩

correct[/%‖]ⁿ : ∀ n₁ n₂ (0<n₂ : 0 < n₂) → let ⟨ quo , rem ⟩ = n₁ /%ⁿ n₂ ‖ 0<n₂ in n₂ × quo + rem ≡ n₁
correct[/%‖]ⁿ n₁ (Succ n₂) Zero with divmod-loop n₁ n₂ 0 n₂ xRx | correct[divmod-loop] n₁ n₂ 0 n₂ xRx
… | ⟨∃ ⟨ quo , n₂-rem ⟩ , n₂-rem≤n₂ ⟩ | H rewrite n-n=0 n₂ | right-unit[+] n₁ | commutative[×] quo (Succ n₂) = H

instance
  DivMod/OK[ℕ] : DivMod/OK ℕ
  DivMod/OK[ℕ] = record
    { ok[_/%_] = (λ n₁ n₂ → 0 < n₂) }
  DivMod[ℕ] : DivMod/P ℕ
  DivMod[ℕ] = record
    { _/%_‖_ = _/%ⁿ_‖_
    ; correct[/%‖] = correct[/%‖]ⁿ
    }

-------------
-- Bounded --
-------------

record ℕ≤[_] (nᵇ : ℕ) : Set where
  constructor mk[ℕ≤]
  field
    n : ℕ
    n≤nᵇ : n ≤ nᵇ

-- mk↯[ℕ≤] : ∀ {nᵇ} n → {{_ : ✓‼ (n ⁇[ _≤_ ] nᵇ)}} → ℕ≤[ nᵇ ]
-- mk↯[ℕ≤] {nᵇ} n {{_}} with n ⁇[ _≤_ ] nᵇ | 
-- mk↯[ℕ≤] {nᵇ} n {{↯Rel}} | Rel n≤nᵇ = mk[ℕ≤] n n≤nᵇ

weaken[ℕ≤] : ∀ {nᵇ₁ nᵇ₂} → nᵇ₁ ≤ nᵇ₂ → ℕ≤[ nᵇ₁ ] → ℕ≤[ nᵇ₂ ]
weaken[ℕ≤] nᵇ₁≤nᵇ₂ (mk[ℕ≤] n n≤nᵇ₁) = mk[ℕ≤] n (nᵇ₁≤nᵇ₂ ⊚ n≤nᵇ₁)

instance
  ToNatural[ℕ≤] : ∀ {nᵇ} → ToNatural ℕ≤[ nᵇ ]
  ToNatural[ℕ≤] = mk[ToNatural] ℕ≤[_].n

record ℕ<[_] (nᵇ : ℕ) : Set where
  constructor mk[ℕ<]
  field
    n : ℕ
    n<nᵇ : n < nᵇ
    
-- mk↯[ℕ<] : ∀ {nᵇ} n → {{_ : rel (dec-rel[ _<_ ] n nᵇ)}} → ℕ<[ nᵇ ]
-- mk↯[ℕ<] {nᵇ} n {{_}} with dec-rel[ _<_ ] n nᵇ
-- mk↯[ℕ<] {nᵇ} n {{↯Rel}} | Rel n<nᵇ = mk[ℕ<] n n<nᵇ

weaken[ℕ<] : ∀ {nᵇ₁ nᵇ₂} → nᵇ₁ ≤ nᵇ₂ → ℕ<[ nᵇ₁ ] → ℕ<[ nᵇ₂ ]
weaken[ℕ<] nᵇ₁≤nᵇ₂ (mk[ℕ<] n n<nᵇ₁) = mk[ℕ<] n $ π₂ rel[</≤]ⁿ $ nᵇ₁≤nᵇ₂ ⊚ π₁ rel[</≤]ⁿ n<nᵇ₁

instance
  ToNatural[ℕ<] : ∀ {nᵇ} → ToNatural ℕ<[ nᵇ ]
  ToNatural[ℕ<] = mk[ToNatural] ℕ<[_].n

data fin : ℕ → Set where
  Zero : ∀ {n} → fin (Succ n)
  Succ : ∀ {n} → fin n → fin (Succ n)

mk[fin/<] : ∀ {nᵇ} n → n < nᵇ → fin nᵇ
mk[fin/<] Zero Zero = Zero
mk[fin/<] (Succ n) (Succ <₁) = Succ (mk[fin/<] n <₁)

mk[fin/ℕ<] : ∀ {nᵇ} → ℕ<[ nᵇ ] → fin nᵇ
mk[fin/ℕ<] (mk[ℕ<] n n<nᵇ) = mk[fin/<] n n<nᵇ

record ℕ⁺ : Set where
  constructor mk[ℕ⁺]
  field
    n : ℕ
    0<n : 0 < n

-- mk↯[ℕ⁺] : ∀ n {{_ : rel (dec-rel[ _<_ ] 0 n)}} → ℕ⁺
-- mk↯[ℕ⁺] n {{_}} with dec-rel[ _<_ ] 0 n
-- mk↯[ℕ⁺] n {{↯Rel}} | Rel 0<n = mk[ℕ⁺] n 0<n

instance
  ToNatural[ℕ⁺] : ToNatural ℕ⁺
  ToNatural[ℕ⁺] = mk[ToNatural] ℕ⁺.n
