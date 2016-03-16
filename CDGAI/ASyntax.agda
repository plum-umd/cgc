module CDGAI.ASyntax where

open import Prelude

context : Set
context = ℕ

data var : context → Set where
  Zero : ∀ {Γ} → var (Succ Γ)
  Succ : ∀ {Γ} → var Γ → var (Succ Γ)

data unary : Set where [+] [-] : unary
data binary : Set where [+] [-] [×] [/] [%] : binary

data aexp (Γ : context) : Set where
  Num : ℤ → aexp Γ
  Var : var Γ → aexp Γ
  ⊤ℤ : aexp Γ
  Unary[_] : unary → aexp Γ → aexp Γ
  Binary[_] : binary → aexp Γ → aexp Γ → aexp Γ
