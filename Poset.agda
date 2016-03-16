module Poset where

open import Prelude

open import Poset.Classes public
open import Poset.Dual public
open import Poset.Fun public
open import Poset.GaloisConnection public
open import Poset.Lib public
open import Poset.Poset public
open import Poset.Power public
open import Poset.PowerMonad public
open import Poset.Product public
open import Poset.ProofMode public

instance
  PreOrder[ℕ] : PreOrder 0ᴸ ℕ
  PreOrder[ℕ] = PreOrder[≡]
  PreOrder[ℤ] : PreOrder 0ᴸ ℤ
  PreOrder[ℤ] = PreOrder[≡]
  PreOrder[𝔹] : PreOrder 0ᴸ 𝔹
  PreOrder[𝔹] = PreOrder[≡]
