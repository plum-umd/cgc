module CDGAI.Syntax where

open import Prelude

context : Set
context = ℕ

data var : context → Set where
  Zero : ∀ {Γ} → var (Suc Γ)
  Suc : ∀ {Γ} → var Γ → var (Suc Γ)

data unary : Set where [+] [-] : unary
data binary : Set where [+] [-] [×] [/] [%] : binary

data aexp (Γ : context) : Set where
  Num : ℤ → aexp Γ
  Var : var Γ → aexp Γ
  ⊤ℤ : aexp Γ
  Unary[_] : unary → aexp Γ → aexp Γ
  Binary[_] : binary → aexp Γ → aexp Γ → aexp Γ
