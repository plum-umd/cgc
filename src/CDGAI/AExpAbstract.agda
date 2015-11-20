module CDGAI.AExpAbstract where

open import Prelude
open import POSet
open import CDGAI.ASyntax
open import CDGAI.ASemantics
open import CDGAI.AEnvAbstract

module §-Faexp♯
  (ℤ♯ : POSet zeroˡ)
  (⇄ℤ⇄ : ⇧ ℤ ⇄ᶜ ℤ♯)
  (⊤ℤ♯ : ⟪ ℤ♯ ⟫)
  (η[⊤ℤ] : (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) * ⋅ all⁺ (⇧ ℤ) ⊑ return ⋅ ⊤ℤ♯)
  (⟦_⟧ᵃ¹♯ : unary → ⟪ ℤ♯ ⇒ ℤ♯ ⟫)
  (α[⟦⟧ᵃ¹] : ∀ {o} → α[ ⇄ℤ⇄ ⇒⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ (pure ⋅ ⟦ o ⟧ᵃ¹⁺) ⊑ pure ⋅ ⟦ o ⟧ᵃ¹♯)
  (⟦_⟧ᵃ²♯ : binary → ⟪ ℤ♯ ⇒ ℤ♯ ⇒ ℤ♯ ⟫)
  (α[⟦⟧ᵃ²] : ∀ {o} → α[ (⇄ℤ⇄ ×⸢⇄ᶜ⸣ ⇄ℤ⇄) ⇒⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²⁺) ⊑ pure ⋅ (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²♯))
  where
  open §-env♯ ℤ♯ ⇄ℤ⇄
  ∃α[⟦⟧ᵃ] :
    ∃ ⟦_⟧ᵃ♯ ⦂ (∀ {Γ} → aexp Γ → ⟪ ⇧ (env♯ Γ) ⇒ ℤ♯ ⟫)
    𝑠𝑡 (∀ {Γ} (e : aexp Γ) → α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟦ e ⟧ᵃ⁺ ⊑ pure ⋅ ⟦ e ⟧ᵃ♯)
  ∃α[⟦⟧ᵃ] = ∃ ⟦_⟧ᵃ♯ ,, α[⟦⟧ᵃ]
    where
      ⟦_⟧ᵃ♯ : ∀ {Γ} → aexp Γ → ⟪ ⇧ (env♯ Γ) ⇒ ℤ♯ ⟫
      ⟦ Num n ⟧ᵃ♯             = const⁺ ⋅ (ηᶜ[ ⇄ℤ⇄ ] ⋅ ↑ n)
      ⟦ Var x ⟧ᵃ♯             = lookup♯[ x ]
      ⟦ ⊤ℤ ⟧ᵃ♯                = const⁺ ⋅ ⊤ℤ♯
      ⟦ Unary[ o ] e ⟧ᵃ♯      = ⟦ o ⟧ᵃ¹♯ ⊙ ⟦ e ⟧ᵃ♯
      ⟦ Binary[ o ] e₁ e₂ ⟧ᵃ♯ = uncurry⁺ ⋅ ⟦ o ⟧ᵃ²♯ ⊙ apply⸢×⁺⸣ ⋅ (⟦ e₁ ⟧ᵃ♯ ,⁺ ⟦ e₂ ⟧ᵃ♯) ⊙ split⁺
      α[⟦⟧ᵃ] : ∀ {Γ} (e : aexp Γ) → α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟦ e ⟧ᵃ⁺ ⊑ pure ⋅ ⟦ e ⟧ᵃ♯
      α[⟦⟧ᵃ] (Num n) = ext[⇒]⸢⊑⸣ $ λ {ρ} → let open §-ProofMode[⊑] in [proof-mode]
        do [[ (α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟦ Num n ⟧ᵃ⁺) ⋅ ρ ]]
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ⟐ ⟦ Num n ⟧ᵃ⁺ ⟐ γᶜ[ ⇄env⇄ ]) ⋅ ρ ]]
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) * ⋅ (⟦ Num n ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ)) ]]
         ‣ [focus-right [⋅] 𝑜𝑓 (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) * ] begin
             do [[ (⟦ Num n ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ)) ]]
              ‣ ⟅ 𝒞⟦Num⟧⸢⊑⸣ ⟆⸢⊑⸣
              ‣ [[ return ⋅ ↑ n ]]
             end
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) * ⋅ (return ⋅ ↑ n) ]]
         ‣ ⟅ right-unit[*] ⟆⸢≈⸣
         ‣ [[ pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ⋅ ↑ n ]]
         ‣ [[ pure ⋅ (const⁺ ⋅ (ηᶜ[ ⇄ℤ⇄ ] ⋅ ↑ n)) ⋅ ρ ]]
         ‣ [[ pure ⋅ ⟦ Num n ⟧ᵃ♯ ⋅ ρ ]]
         ∎ 
      α[⟦⟧ᵃ] (Var x) = let open §-ProofMode[⊑] in [proof-mode]
        do [[ α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟦ Var x ⟧ᵃ⁺ ]]
         ‣ [[ pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ⟐ ⟦ Var x ⟧ᵃ⁺ ⟐ γᶜ[ ⇄env⇄ ] ]]
         ‣ [focus-right [⟐] 𝑜𝑓 pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ] begin
             do [focus-left [⟐] 𝑜𝑓 γᶜ[ ⇄env⇄ ] ] begin
                  do [[ ⟦ Var x ⟧ᵃ⁺ ]]
                   ‣ ⟅ 𝒞⟦Var⟧⸢⊙⸣ ⟆⸢≈⸣
                   ‣ [[ pure ⋅ lookup[ x ]⁺ ]]
                  end
              ‣ [[ pure ⋅ lookup[ x ]⁺ ⟐ γᶜ[ ⇄env⇄ ] ]]
              ‣ ⟅ π₁ α[f]↔f⟐γᶜ[ ⇄env⇄ , ⇄ℤ⇄ ] $ α[lookup] {x = x} ⟆
              ‣ [[ γᶜ[ ⇄ℤ⇄ ] ⟐ pure ⋅ lookup♯[ x ] ]]
             end
         ‣ [[ pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ⟐ γᶜ[ ⇄ℤ⇄ ] ⟐ pure ⋅ lookup♯[ x ] ]]
         ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ⟐ γᶜ[ ⇄ℤ⇄ ]) ⟐ pure ⋅ lookup♯[ x ] ]]
         ‣ ⟅ left-unit-contractive[⟐]ᶜ[ ⇄ℤ⇄ ] ⟆
         ‣ [[ pure ⋅ lookup♯[ x ] ]]
         ‣ [[ pure ⋅ ⟦ Var x ⟧ᵃ♯ ]]
         ∎ 
      α[⟦⟧ᵃ] ⊤ℤ = ext[⇒]⸢⊑⸣ $ λ {ρ} → let open §-ProofMode[⊑] in [proof-mode]
        do [[ (α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟦ ⊤ℤ ⟧ᵃ⁺) ⋅ ρ ]]
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ⟐ ⟦ ⊤ℤ ⟧ᵃ⁺ ⟐ γᶜ[ ⇄env⇄ ]) ⋅ ρ ]]
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) * ⋅ (⟦ ⊤ℤ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ)) ]]
         ‣ [focus-right [⋅] 𝑜𝑓 (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) * ] begin
             do [[ (⟦ ⊤ℤ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ)) ]]
              ‣ ⟅ 𝒞⟦⊤ℤ⟧⸢⊑⸣ ⟆
              ‣ [[ all⁺ (⇧ ℤ) ]]
             end
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) * ⋅ all⁺ (⇧ ℤ) ]]
         ‣ ⟅ η[⊤ℤ] ⟆
         ‣ [[ return ⋅ ⊤ℤ♯ ]]
         ‣ [[ pure ⋅ ⟦ ⊤ℤ ⟧ᵃ♯ ⋅ ρ ]]
         ∎ 
      α[⟦⟧ᵃ] (Unary[ o ] e) with α[⟦⟧ᵃ] e
      ... | IH = let open §-ProofMode[⊑] in [proof-mode]
        do [[ α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟦ Unary[ o ] e ⟧ᵃ⁺ ]]
         ‣ [[ pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ⟐ ⟦ Unary[ o ] e ⟧ᵃ⁺ ⟐ γᶜ[ ⇄env⇄ ] ]]
         ‣ [focus-right [⟐] 𝑜𝑓 pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ] begin
             do [focus-left [⟐] 𝑜𝑓 γᶜ[ ⇄env⇄ ] ] begin
                  do [[ ⟦ Unary[ o ] e ⟧ᵃ⁺ ]]
                   ‣ ⟅ 𝒞⟦Unary⟧⸢⟐⸣ ⟆⸢≈⸣
                   ‣ [[ pure ⋅ ⟦ o ⟧ᵃ¹⁺ ⟐ ⟦ e ⟧ᵃ⁺ ]]
                  end
              ‣ [[ (pure ⋅ ⟦ o ⟧ᵃ¹⁺ ⟐ ⟦ e ⟧ᵃ⁺) ⟐ γᶜ[ ⇄env⇄ ] ]]
              ‣ ⟅ associative[⟐] ⟆⸢≈⸣
              ‣ [[ pure ⋅ ⟦ o ⟧ᵃ¹⁺ ⟐ ⟦ e ⟧ᵃ⁺ ⟐ γᶜ[ ⇄env⇄ ] ]]
              ‣ [focus-right [⟐] 𝑜𝑓 pure ⋅ ⟦ o ⟧ᵃ¹⁺ ] begin
                  do [[ ⟦ e ⟧ᵃ⁺ ⟐ γᶜ[ ⇄env⇄ ] ]]
                   ‣ ⟅ π₁ α[f]↔f⟐γᶜ[ ⇄env⇄ , ⇄ℤ⇄ ] IH ⟆
                   ‣ [[ γᶜ[ ⇄ℤ⇄ ] ⟐ pure ⋅ ⟦ e ⟧ᵃ♯ ]]
                  end
              ‣ [[ pure ⋅ ⟦ o ⟧ᵃ¹⁺ ⟐ γᶜ[ ⇄ℤ⇄ ] ⟐ pure ⋅ ⟦ e ⟧ᵃ♯ ]]
              ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
              ‣ [[ (pure ⋅ ⟦ o ⟧ᵃ¹⁺ ⟐ γᶜ[ ⇄ℤ⇄ ]) ⟐ pure ⋅ ⟦ e ⟧ᵃ♯ ]]
              ‣ [focus-left [⟐] 𝑜𝑓 pure ⋅ ⟦ e ⟧ᵃ♯ ] begin
                  do [[ pure ⋅ ⟦ o ⟧ᵃ¹⁺ ⟐ γᶜ[ ⇄ℤ⇄ ] ]]
                   ‣ ⟅ π₁ α[f]↔f⟐γᶜ[ ⇄ℤ⇄ , ⇄ℤ⇄ ] α[⟦⟧ᵃ¹] ⟆
                   ‣ [[ γᶜ[ ⇄ℤ⇄ ] ⟐ pure ⋅ ⟦ o ⟧ᵃ¹♯ ]]
                  end
              ‣ [[ (γᶜ[ ⇄ℤ⇄ ] ⟐ pure ⋅ ⟦ o ⟧ᵃ¹♯) ⟐ pure ⋅ ⟦ e ⟧ᵃ♯ ]]
              ‣ ⟅ associative[⟐] ⟆⸢≈⸣
              ‣ [[ γᶜ[ ⇄ℤ⇄ ] ⟐ pure ⋅ ⟦ o ⟧ᵃ¹♯ ⟐ pure ⋅ ⟦ e ⟧ᵃ♯ ]]
             end
         ‣ [[ pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ⟐ γᶜ[ ⇄ℤ⇄ ] ⟐ pure ⋅ ⟦ o ⟧ᵃ¹♯ ⟐ pure ⋅ ⟦ e ⟧ᵃ♯ ]]
         ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ⟐ γᶜ[ ⇄ℤ⇄ ]) ⟐ pure ⋅ ⟦ o ⟧ᵃ¹♯ ⟐ pure ⋅ ⟦ e ⟧ᵃ♯ ]]
         ‣ ⟅ left-unit-contractive[⟐]ᶜ[ ⇄ℤ⇄ ] ⟆
         ‣ [[ pure ⋅ ⟦ o ⟧ᵃ¹♯ ⟐ pure ⋅ ⟦ e ⟧ᵃ♯ ]]
         ‣ ⟅ homomorphic[pure]⸢⟐⸣ ⟆⸢≈⸣
         ‣ [[ pure ⋅ (⟦ o ⟧ᵃ¹♯ ⊙ ⟦ e ⟧ᵃ♯) ]]
         ‣ [[ pure ⋅ ⟦ Unary[ o ] e ⟧ᵃ♯ ]]
         ∎
      α[⟦⟧ᵃ] (Binary[ o ] e₁ e₂) with α[⟦⟧ᵃ] e₁ | α[⟦⟧ᵃ] e₂
      ... | IH₁ | IH₂ = ext[⇒]⸢⊑⸣ $ λ {ρ} → let open §-ProofMode[⊑] in [proof-mode]
        do [[ (α[ ⇄env⇄ ⇒⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟦ Binary[ o ] e₁ e₂ ⟧ᵃ⁺) ⋅ ρ ]]
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ] ⟐ ⟦ Binary[ o ] e₁ e₂ ⟧ᵃ⁺ ⟐ γᶜ[ ⇄env⇄ ]) ⋅ ρ ]]
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) * ⋅ (⟦ Binary[ o ] e₁ e₂ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ)) ]]
         ‣ [focus-right [⋅] 𝑜𝑓 (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) * ] begin
             do [[ ⟦ Binary[ o ] e₁ e₂ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ) ]]
              ‣ ⟅ 𝒞⟦Binary⟧⸢*⸣⸢⊑⸣ ⟆
              ‣ [[ (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²⁺) * ⋅ (γ⸢IA⸣ ⋅ (⟦ e₁ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ) ,⁺ ⟦ e₂ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ))) ]]
              ‣ [focus-right [⋅] 𝑜𝑓 (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²⁺) * ] begin
                  do [focus-right [⋅] 𝑜𝑓 γ⸢IA⸣ ] begin
                       do [[ ⟦ e₁ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ) ,⁺ ⟦ e₂ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ) ]]
                        ‣ [focus-left [,] 𝑜𝑓 ⟦ e₂ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ) ] begin
                            do [[ ⟦ e₁ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ) ]]
                             ‣ ⟅ π₁ α[f]↔f⟐γᶜ*[ ⇄env⇄ , ⇄ℤ⇄ ] IH₁ ⟆
                             ‣ [[ γᶜ[ ⇄ℤ⇄ ] * ⋅ (pure ⋅ ⟦ e₁ ⟧ᵃ♯ ⋅ ρ) ]]
                             end
                        ‣ [[ γᶜ[ ⇄ℤ⇄ ] * ⋅ (pure ⋅ ⟦ e₁ ⟧ᵃ♯ ⋅ ρ) ,⁺ ⟦ e₂ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ) ]]
                        ‣ [focus-right [,] 𝑜𝑓 γᶜ[ ⇄ℤ⇄ ] * ⋅ (pure ⋅ ⟦ e₁ ⟧ᵃ♯ ⋅ ρ) ] begin
                            do [[ ⟦ e₂ ⟧ᵃ⁺ * ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ) ]]
                             ‣ ⟅ π₁ α[f]↔f⟐γᶜ*[ ⇄env⇄ , ⇄ℤ⇄ ] IH₂ ⟆
                             ‣ [[ γᶜ[ ⇄ℤ⇄ ] * ⋅ (pure ⋅ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ) ]]
                            end
                        ‣ [[ γᶜ[ ⇄ℤ⇄ ] * ⋅ (pure ⋅ ⟦ e₁ ⟧ᵃ♯ ⋅ ρ) ,⁺ γᶜ[ ⇄ℤ⇄ ] * ⋅ (pure ⋅ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ) ]]
                       end
                   ‣ [[ γ⸢IA⸣ ⋅ (γᶜ[ ⇄ℤ⇄ ] * ⋅ (pure ⋅ ⟦ e₁ ⟧ᵃ♯ ⋅ ρ) ,⁺ γᶜ[ ⇄ℤ⇄ ] * ⋅ (pure ⋅ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ)) ]]
                   ‣ ⟅ homomorphic[γ/γ]⸢IA⸣[ ⇄ℤ⇄ , ⇄ℤ⇄ ] ⟆⸢≈⸣
                   ‣ [[ γᶜ[ ⇄ℤ⇄ ×⸢⇄ᶜ⸣ ⇄ℤ⇄ ] * ⋅ (γ⸢IA⸣ ⋅ (pure ⋅ ⟦ e₁ ⟧ᵃ♯ ⋅ ρ ,⁺ pure ⋅ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ)) ]]
                   ‣ [[ γᶜ[ ⇄ℤ⇄ ×⸢⇄ᶜ⸣ ⇄ℤ⇄ ] * ⋅ (γ⸢IA⸣ ⋅ (return ⋅ (⟦ e₁ ⟧ᵃ♯ ⋅ ρ) ,⁺ return ⋅ (⟦ e₂ ⟧ᵃ♯ ⋅ ρ))) ]]
                   ‣ [focus-right [⋅] 𝑜𝑓 γᶜ[ ⇄ℤ⇄ ×⸢⇄ᶜ⸣ ⇄ℤ⇄ ] * ] begin
                       do [[ γ⸢IA⸣ ⋅ (return ⋅ (⟦ e₁ ⟧ᵃ♯ ⋅ ρ) ,⁺ return ⋅ (⟦ e₂ ⟧ᵃ♯ ⋅ ρ)) ]]
                        ‣ ⟅ homomorphic[γ/return]⸢IA⸣ ⟆⸢≈⸣
                        ‣ [[ return ⋅ (⟦ e₁ ⟧ᵃ♯ ⋅ ρ ,⁺ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ) ]]
                       end
                   ‣ [[ γᶜ[ ⇄ℤ⇄ ×⸢⇄ᶜ⸣ ⇄ℤ⇄ ] * ⋅ (return ⋅ (⟦ e₁ ⟧ᵃ♯ ⋅ ρ ,⁺ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ)) ]]
                  end
              ‣ [[ (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²⁺) * ⋅ (γᶜ[ ⇄ℤ⇄ ×⸢⇄ᶜ⸣ ⇄ℤ⇄ ] * ⋅ (return ⋅ (⟦ e₁ ⟧ᵃ♯ ⋅ ρ ,⁺ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ))) ]]
              ‣ ⟅ π₁ α[f]↔f⟐γᶜ*X[ ⇄ℤ⇄ ×⸢⇄ᶜ⸣ ⇄ℤ⇄ , ⇄ℤ⇄ ] α[⟦⟧ᵃ²] ⟆
              ‣ [[ γᶜ[ ⇄ℤ⇄ ] * ⋅ ((pure ⋅ (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²♯)) * ⋅ (return ⋅ (⟦ e₁ ⟧ᵃ♯ ⋅ ρ ,⁺ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ))) ]]
             end
         ‣ [[ (pure ⋅ ηᶜ[ ⇄ℤ⇄ ]) * ⋅ (γᶜ[ ⇄ℤ⇄ ] * ⋅ ((pure ⋅ (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²♯)) * ⋅ (return ⋅ (⟦ e₁ ⟧ᵃ♯ ⋅ ρ ,⁺ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ)))) ]]
         ‣ ⟅ contractiveᶜ[X*][ ⇄ℤ⇄ ] ⟆
         ‣ [[ (pure ⋅ (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²♯)) * ⋅ (return ⋅ (⟦ e₁ ⟧ᵃ♯ ⋅ ρ ,⁺ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ)) ]]
         ‣ ⟅ right-unit[*] ⟆⸢≈⸣
         ‣ [[ pure ⋅ (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²♯) ⋅ (⟦ e₁ ⟧ᵃ♯ ⋅ ρ ,⁺ ⟦ e₂ ⟧ᵃ♯ ⋅ ρ) ]]
         ‣ [[ pure ⋅ (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²♯) ⋅ ((apply⸢×⁺⸣ ⋅ (⟦ e₁ ⟧ᵃ♯ ,⁺ ⟦ e₂ ⟧ᵃ♯)  ⊙ split⁺) ⋅ ρ) ]]
         ‣ ⟅ ◇ $ homomorphic[pure] {g = (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²♯)} {f = apply⸢×⁺⸣ ⋅ (⟦ e₁ ⟧ᵃ♯ ,⁺ ⟦ e₂ ⟧ᵃ♯) ⊙ split⁺} ⟆⸢≈⸣
         ‣ [[ pure ⋅ (uncurry⁺ ⋅ ⟦ o ⟧ᵃ²♯ ⊙ apply⸢×⁺⸣ ⋅ (⟦ e₁ ⟧ᵃ♯ ,⁺ ⟦ e₂ ⟧ᵃ♯) ⊙ split⁺) ⋅ ρ ]]
         ‣ [[ pure ⋅ ⟦ Binary[ o ] e₁ e₂ ⟧ᵃ♯ ⋅ ρ ]]
         ∎