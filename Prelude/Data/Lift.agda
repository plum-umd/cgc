module Prelude.Data.Lift where

open import Prelude.Core

record lift ℓ {ℓ'} (A : Set ℓ') : Set (ℓ ⊔ᴸ ℓ') where
  constructor mk[lift]
  field un[lift] : A
open lift public
