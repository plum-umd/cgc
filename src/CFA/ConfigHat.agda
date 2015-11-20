module CFA.ConfigHat where

open import Prelude
open import POSet

open import CFA.Syntax
open import CFA.Semantics
open import CFA.EnvHat

-- data config^ Γ : Set where
--   ⟨_,_⟩ : call Γ → env^ Γ → config^ Γ
-- 
-- data _⊴⸢config^⸣_ {Γ} : relation zeroˡ (config^ Γ) where
--   ↑⟨_⟩ : ∀ {c ρ₁ ρ₂} → ρ₁ ⊴ ρ₂ → ⟨ c , ρ₁ ⟩ ⊴⸢config^⸣ ⟨ c , ρ₂ ⟩
-- 
-- xRx⸢⊴⸢config^⸣⸣ : ∀ {Γ} → reflexive (_⊴⸢config^⸣_ {Γ})
-- xRx⸢⊴⸢config^⸣⸣ {x = ⟨ c , ρ ⟩} = ↑⟨ xRx ⟩
-- 
-- _⌾⸢⊴⸢config^⸣⸣_ : ∀ {Γ} → transitive (_⊴⸢config^⸣_ {Γ})
-- ↑⟨ ρ₂⊴ρ₃ ⟩ ⌾⸢⊴⸢config^⸣⸣ ↑⟨ ρ₁⊴ρ₂ ⟩ = ↑⟨ ρ₂⊴ρ₃ ⌾ ρ₁⊴ρ₂ ⟩
-- 
-- instance
--   Reflexive[⊴⸢config^⸣] : ∀ {Γ} → Reflexive (_⊴⸢config^⸣_ {Γ})
--   Reflexive[⊴⸢config^⸣] = record { xRx = xRx⸢⊴⸢config^⸣⸣ }
--   Transitive[⊴⸢config^⸣] : ∀ {Γ} → Transitive (_⊴⸢config^⸣_ {Γ})
--   Transitive[⊴⸢config^⸣] = record { _⌾_ = _⌾⸢⊴⸢config^⸣⸣_ }
--   PreOrder[config^] : ∀ {Γ} → PreOrder zeroˡ (config^ Γ)
--   PreOrder[config^] = record { _⊴_ = _⊴⸢config^⸣_ }
-- 
-- α⸢config⸣ : ∀ {Γ} → config Γ → config^ Γ
-- α⸢config⸣ ⟨ e , ρ ⟩ = ⟨ e , ↓ (η[ ⇄env⇄ ] ⋅ ↑ ρ) ⟩
-- 
-- monotonic[α⸢config⸣] : ∀ {Γ} {ς₁ ς₂ : config Γ} → ς₁ ⊴ ς₂ → α⸢config⸣ ς₁ ⊴ α⸢config⸣ ς₂
-- monotonic[α⸢config⸣] ↯ = xRx
-- 
-- data γ⸢config⸣ {Γ} : config^ Γ → config Γ → Set where
--   ↑⟨_⟩ : ∀ {e ρ^ ρ} → ↑ ρ ⋿ γ⸢η⸣[ ⇄env⇄ ] ⋅ ↑ ρ^ → γ⸢config⸣ ⟨ e , ρ^ ⟩ ⟨ e , ρ ⟩
-- 
-- monotonic[γ⸢config⸣] : ∀ {Γ} {ς₁^ ς₂^ : config^ Γ} → ς₁^ ⊴ ς₂^ → ∀ {ς₁ ς₂ : config Γ} → ς₂ ⊴ ς₁ → γ⸢config⸣ ς₁^ ς₁ → γ⸢config⸣ ς₂^ ς₂
-- monotonic[γ⸢config⸣] ↑⟨ ρ₁^⊴ρ₂^ ⟩ ↯ ↑⟨ ρ∈γ[ρ₁^] ⟩ = ↑⟨ (res-X[ω]⸢⊑⸣ {x = ↑⟨ _ ⟩} (res-x[λ]⸢⊑⸣ {f = γ⸢η⸣[ ⇄env⇄ ]} ↑⟨ ρ₁^⊴ρ₂^ ⟩) ρ∈γ[ρ₁^]) ⟩
-- 
-- αγ-sound⸢config⸣ : ∀ {Γ} (ς : config Γ) → γ⸢config⸣ (α⸢config⸣ ς) ς
-- αγ-sound⸢config⸣ ⟨ e , ρ ⟩ = ↑⟨ sound⸢η⸣[ ⇄env⇄ ] {x = ↑ ρ} ⟩
-- 
-- αγ-complete⸢config⸣ : ∀ {Γ} {ς : config Γ} {ς^ : config^ Γ} → γ⸢config⸣ ς^ ς → α⸢config⸣ ς ⊴ ς^
-- αγ-complete⸢config⸣ {ς = ⟨ e , ρ ⟩} {⟨ .e , ρ^ ⟩} ↑⟨ ρ∈γ[ρ^] ⟩ = ↑⟨ H $ complete⸢η⸣[ ⇄env⇄ ] {x^ = ↑ ρ^} {↑ ρ} ρ∈γ[ρ^] ⟩
--   where
--     H : ∀ {Γ} {ρ₁ ρ₂ : env^ Γ} → ↑ ρ₁ ⊑ ↑ ρ₂ → ρ₁ ⊴ ρ₂
--     H ↑⟨ ρ₁⊴ρ₂ ⟩ = ρ₁⊴ρ₂
-- 
-- ⇄config⇄ : ∀ {Γ} → ⇧ (config Γ) η⇄γ ⇧ (config^ Γ)
-- ⇄config⇄ = mk[η⇄γ]⸢↑⸣ record
--   { η⸢↑⸣ = α⸢config⸣
--   ; monotonic[η⸢↑⸣] = monotonic[α⸢config⸣]
--   ; γ⸢↑⸣ = γ⸢config⸣
--   ; monotonic[γ⸢↑⸣] = monotonic[γ⸢config⸣]
--   ; sound[ηγ]⸢↑⸣ = λ {x} → αγ-sound⸢config⸣ x
--   ; complete[ηγ]⸢↑⸣ = αγ-complete⸢config⸣
--   }
-- 
-- -- Ordered Universe --
-- 
-- config^→prod : ∀ {Γ} → ⟪ ⇧ (config^ Γ) ⇒ ⇧ (call Γ) ⟨×⟩ ⇧ (env^ Γ) ⟫
-- config^→prod {Γ} = witness-x (curry⸢λ↑⸣ id⸢λ↑⸣) $ mk[witness] fun ppr
--   where
--     fun : config^ Γ → prod (⇧ (call Γ)) (⇧ (env^ Γ))
--     fun ⟨ c , ρ^ ⟩ = ↑⟨ c ⟩ , ↑⟨ ρ^ ⟩
--     abstract
--       ppr : proper (_⊴_ ⇉ _⊴_) fun
--       ppr {⟨ c , ρ₁ ⟩} {⟨ .c , ρ₂ ⟩} ↑⟨ ρ₁⊑ρ₂ ⟩ = ↑⟨ ↯ ⟩ , ↑⟨ ρ₁⊑ρ₂ ⟩
