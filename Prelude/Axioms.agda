module Prelude.Axioms where

open import Prelude.Core

module Extensionality where
  postulate
    ext[≡] : ∀ {ℓ} {A B : Set ℓ} (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g
