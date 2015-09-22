module POSet where

open import Prelude

open import POSet.Classes public
open import POSet.Dual public
open import POSet.FSet public
open import POSet.Fun public
open import POSet.GaloisConnection public
open import POSet.Lib public
open import POSet.POSet public
open import POSet.Power public
open import POSet.PowerMonad public
open import POSet.Product public
open import POSet.ProofMode public
open import POSet.Prp public

instance
  PreOrder[ℕ] : PreOrder zeroˡ ℕ
  PreOrder[ℕ] = ≡-PreOrder
  PreOrder[ℤ] : PreOrder zeroˡ ℤ
  PreOrder[ℤ] = ≡-PreOrder
