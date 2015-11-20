module CFA.StepsHat where

open import Prelude
open import POSet

open import CFA.Syntax
open import CFA.Semantics
open import CFA.ValueHat
open import CFA.EnvHat
open import CFA.ConfigHat

-- postulate
--   pure⸢ND⸣ : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ (A ⇒ ⇧ (list-set ⟪ B ⟫)) ⇒ (A ⇒ 𝒫 B) ⟫
-- 
-- α[steps] :
--   ∃ steps^ ⦂ (∀ {Γ} → ⟪ ⇧ (config^ Γ) ⇒ ⇧ (list-set ⟪ ⇧ (config^ Γ) ⟫) ⟫)
--   𝑠𝑡 (∀ {Γ} → α[ ⇄config⇄ ⇒⸢η⇄γ⸣ ⇄config⇄ ] ⋅ steps {Γ} ⊑ pure⸢ND⸣ ⋅ steps^ {Γ})
-- α[steps] = ∃ steps^ ,, ext[λ]⸢⊑⸣ proof
--   where
--     postulate
--       steps^ : ∀ {Γ} → ⟪ ⇧ (config^ Γ) ⇒ ⇧ (list-set ⟪ ⇧ (config^ Γ) ⟫) ⟫
--     proof : ∀ {Γ} {ς^ : ⟪ ⇧ (config^ Γ) ⟫} → α[ ⇄config⇄ ⇒⸢η⇄γ⸣ ⇄config⇄ ] ⋅ steps ⋅ ς^ ⊑ pure⸢ND⸣ ⋅ steps^ ⋅ ς^
--     proof {ς^ = ↑⟨ ⟨ Apply fa₁ fa₂ ka , ρ^ ⟩ ⟩} = [⊑-proof-mode]
--       do [⊑][[ α[ ⇄config⇄ ⇒⸢η⇄γ⸣ ⇄config⇄ ] ⋅ steps ⋅ ↑⟨ ⟨ Apply fa₁ fa₂ ka , ρ^ ⟩ ⟩ ]]
--       ⊑‣ [⊑-≡] (pure ⋅ η[ ⇄config⇄ ]) * ⋅ (steps * ⋅ (γ⸢η⸣[ ⇄config⇄ ] ⋅ ↑⟨ ⟨ Apply fa₁ fa₂ ka , ρ^ ⟩ ⟩ )) ⟅ ↯ ⟆
--       ⊑‣ [⊑-≡] (pure ⋅ η[ ⇄config⇄ ]) * ⋅ (steps * ⋅ ((pure ⋅ prod→config^) * ⋅ (γ[IA] ⋅ (return ⋅ ↑⟨ Apply fa₁ fa₂ ka ⟩ ⟨,⟩ γ⸢η⸣[ ⇄config⇄ ] ⋅ ρ^))) ⟅ ? ⟆
--       ⊑‣ [⊑]   (pure ⋅ η[ ⇄config⇄ ]) * ⋅ (λ ρ^ → ⟦ fa₁ ⟧^ ρ >>= λ v → decide v-is-clo → step-impl)
--       ⊑‣ [⊑-≡] (pure ⋅ η[ ⇄config⇄ ]) * $
--                steps * $
--                (pure ⋅ prod→config^) * $
--                γ⸢η⸣[ id⸢η⇄γ⸣ ×⸢η⇄γ⸣ ⇄config⇄ ] * $
--                (pure ⋅ η[IA]) * $
--                (γ[IA] ⋅ (↑⟨ Apply fa₁ fa₂ ka ⟩ ⟨,⟩ ↑⟨ ρ^ ⟩)) ⟅ ? ⟆
--       ⊑‣ {!!}
--       ⊑‣ [⊑][[ pure⸢ND⸣ ⋅ steps^ ⋅ ↑⟨ ⟨ Apply fa₁ fa₂ ka , ρ^ ⟩ ⟩ ]]
--       ⬜
--     proof {ς^ = ↑⟨ ⟨ Call ka fa , ρ ⟩ ⟩} = {!!}
