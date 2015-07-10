module OSet where

open import Prelude

open import OSet.OSet public
open import OSet.Fun public
open import OSet.Power public
open import OSet.Product public
open import OSet.Promote public
open import OSet.Classes public
open import OSet.ProofMode public
open import OSet.Lib public
open import OSet.GaloisConnection public
open import OSet.FSet public

instance
  PreOrder[ℕ] : PreOrder zeroˡ ℕ
  PreOrder[ℕ] = ≡-PreOrder
  PreOrder[ℤ] : PreOrder zeroˡ ℤ
  PreOrder[ℤ] = ≡-PreOrder
