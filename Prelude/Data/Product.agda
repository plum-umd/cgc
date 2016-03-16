module Prelude.Data.Product where

open import Prelude.Core
open import Prelude.Relations
open import Prelude.Classes

-- module _ {ℓ₁ ℓ₁ʳ ℓ₂ ℓ₂ʳ} {A : Set ℓ₁} {{_ : PreOrder ℓ₁ʳ A}} {B : Set ℓ₂} {{_ : PreOrder ℓ₂ʳ B}} where
--   data _≼ˣ_ : A ∧ B → A ∧ B → Set (ℓ₁ ⊔ᴸ ℓ₂ ⊔ᴸ ℓ₁ʳ ⊔ᴸ ℓ₂ʳ) where
--     _,_ : ∀ {x₁ y₁ x₂ y₂} → x₁ ≼ x₂ → y₁ ≼ y₂ → (x₁ , y₁) ≼ˣ (x₂ , y₂)
-- 
--   xRx⸢≼ˣ⸣ : reflexive _≼ˣ_
--   xRx⸢≼ˣ⸣ {_ , _} = xRx⸢≼⸣ , xRx⸢≼⸣
-- 
--   _⊚⸢≼ˣ⸣_ : transitive _≼ˣ_
--   (≼₁₁ , ≼₂₁) ⊚⸢≼ˣ⸣ (≼₁₂ , ≼₂₂) = ≼₁₁ ⊚⸢≼⸣ ≼₁₂ , ≼₂₁ ⊚⸢≼⸣ ≼₂₂
-- 
--   instance
--     Reflexive[≼ˣ] : Reflexive _≼ˣ_
--     Reflexive[≼ˣ] = record { xRx = xRx⸢≼ˣ⸣ }
--     Transitive[≼ˣ] : Transitive _≼ˣ_
--     Transitive[≼ˣ] = record { _⊚_ = _⊚⸢≼ˣ⸣_ }
--     PreOrder[×] : PreOrder (ℓ₁ ⊔ᴸ ℓ₂ ⊔ᴸ ℓ₁ʳ ⊔ᴸ ℓ₂ʳ) (A ∧ B)
--     PreOrder[×] = record { _≼_ = _≼ˣ_ }
