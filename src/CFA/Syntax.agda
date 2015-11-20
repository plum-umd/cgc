module CFA.Syntax where

open import Prelude

context : Set
context = ℕ

data var : context → Set where
  Zero : ∀ {Γ} → var (Suc Γ)
  Suc : ∀ {Γ} → var Γ → var (Suc Γ)

data _≤⸢Γ⸣_ : context → context → Set where
  Zero : ∀ {Γ} → Γ ≤⸢Γ⸣ Γ
  Suc : ∀ {Γ₁ Γ₂} → Γ₁ ≤⸢Γ⸣ Γ₂ → Γ₁ ≤⸢Γ⸣ Suc Γ₂

inj-suc-≤⸢Γ⸣ : ∀ {Γ₁ Γ₂} → Suc Γ₁ ≤⸢Γ⸣ Suc Γ₂ → Γ₁ ≤⸢Γ⸣ Γ₂
inj-suc-≤⸢Γ⸣ Zero = Zero
inj-suc-≤⸢Γ⸣ {Γ₂ = Zero} (Suc ())
inj-suc-≤⸢Γ⸣ {Γ₂ = Suc Γ₂} (Suc φ) = Suc (inj-suc-≤⸢Γ⸣ φ)

suc-≤⸢Γ⸣ : ∀ {Γ₁ Γ₂} → Suc Γ₁ ≤⸢Γ⸣ Γ₂ → Γ₁ ≤⸢Γ⸣ Γ₂
suc-≤⸢Γ⸣ Zero = Suc Zero
suc-≤⸢Γ⸣ (Suc φ) = Suc (suc-≤⸢Γ⸣ φ)

suc⸢var⸣ : ∀ {Γ} → var Γ → var (Suc Γ)
suc⸢var⸣ Zero = Suc Zero
suc⸢var⸣ (Suc x) = Suc (suc⸢var⸣ x)

rename⸢var⸣ : ∀ {Γ Γ'} → Γ ≤⸢Γ⸣ Γ' → var Γ → var Γ'
rename⸢var⸣ Zero x = x
rename⸢var⸣ (Suc φ) x = Suc (rename⸢var⸣ φ x)

rename-suc⸢var⸣-≡ : ∀ {Γ₁ Γ₂} (H : Suc Γ₁ ≤⸢Γ⸣ Γ₂) (x : var Γ₁) → rename⸢var⸣ (suc-≤⸢Γ⸣ H) x ≡ rename⸢var⸣ H (Suc x)
rename-suc⸢var⸣-≡ Zero x = ↯
rename-suc⸢var⸣-≡ (Suc φ) x rewrite rename-suc⸢var⸣-≡ φ x = ↯

mutual
  data atom Γ : Set where
    Var  : var Γ → atom Γ
    FLam : var Γ → var Γ → call Γ → atom Γ
    KLam : var Γ → call Γ → atom Γ
  data call Γ : Set where
    Apply : atom Γ → atom Γ → atom Γ → call Γ
    Call  : atom Γ → atom Γ → call Γ

instance
  PreOrder[call] : ∀ {Γ} → PreOrder zeroˡ (call Γ)
  PreOrder[call] = ≡-PreOrder

mutual
  suc⸢atom⸣ : ∀ {Γ} → atom Γ → atom (Suc Γ)
  suc⸢atom⸣ (Var x) = Var (suc⸢var⸣ x)
  suc⸢atom⸣ (FLam x k c) = FLam (suc⸢var⸣ x) (suc⸢var⸣ k) (suc⸢call⸣ c)
  suc⸢atom⸣ (KLam x c) = KLam (suc⸢var⸣ x) (suc⸢call⸣ c)

  suc⸢call⸣ : ∀ {Γ} → call Γ → call (Suc Γ)
  suc⸢call⸣ (Apply fa₁ fa₂ ka) = Apply (suc⸢atom⸣ fa₁) (suc⸢atom⸣ fa₂) (suc⸢atom⸣ ka)
  suc⸢call⸣ (Call ka fa) = Call (suc⸢atom⸣ ka) (suc⸢atom⸣ fa)
  
program : context → Set
program Γ = call Γ
