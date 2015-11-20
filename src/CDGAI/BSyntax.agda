module CDGAI.BSyntax where

open import CDGAI.ASyntax

data comparison : Set where [≟] [⩻] : comparison
data logical : Set where [∨] [∧] : logical

data bexp (Γ : context) : Set where
  True : bexp Γ
  False : bexp Γ
  Compare[_] : comparison → aexp Γ → aexp Γ → bexp Γ
  Logical[_] : logical → bexp Γ → bexp Γ → bexp Γ
