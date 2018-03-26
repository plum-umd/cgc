module CDGAI.EnvAbstraction where

open import Prelude
open import Poset
open import CDGAI.ASyntax
open import CDGAI.ASemantics
open import CDGAI.ZAbstraction

data env♯ : context → Set where
  [] : env♯ zero
  _∷_ : ∀ {Γ} → ⟪ ℤ♯ ⟫ → env♯ Γ → env♯ (Succ Γ)

data _≼⸢env♯⸣_ : ∀ {Γ} → relation 0ᴸ (env♯ Γ) where
  [] : [] ≼⸢env♯⸣ []
  _∷_ : ∀ {Γ} {ρ₁ ρ₂ : env♯ Γ} {n₁ n₂ }→ n₁ ⊑♮ n₂ → ρ₁ ≼⸢env♯⸣ ρ₂ → (n₁ ∷ ρ₁) ≼⸢env♯⸣ (n₂ ∷ ρ₂)

xRx⸢≼⸢env♯⸣⸣ : ∀ {Γ} → reflexive (_≼⸢env♯⸣_ {Γ})
xRx⸢≼⸢env♯⸣⸣ {x = []} = []
xRx⸢≼⸢env♯⸣⸣ {x = n ∷ ρ} = xRx ∷ xRx⸢≼⸢env♯⸣⸣

_⊚⸢≼⸢env♯⸣⸣_ : ∀ {Γ} → transitive (_≼⸢env♯⸣_ {Γ})
[] ⊚⸢≼⸢env♯⸣⸣ [] = []
(n₂⊑n₃ ∷ ρ₂⊑ρ₃) ⊚⸢≼⸢env♯⸣⸣ (n₁⊑n₂ ∷ ρ₁⊑ρ₂) = (n₂⊑n₃ ⊚ n₁⊑n₂) ∷ (ρ₂⊑ρ₃ ⊚⸢≼⸢env♯⸣⸣ ρ₁⊑ρ₂)

instance
  Reflexive[≼⸢env♯⸣] : ∀ {Γ} → Reflexive (_≼⸢env♯⸣_ {Γ})
  Reflexive[≼⸢env♯⸣] = record { xRx = xRx⸢≼⸢env♯⸣⸣ }
  Transitive[≼⸢env♯⸣] : ∀ {Γ} → Transitive (_≼⸢env♯⸣_ {Γ})
  Transitive[≼⸢env♯⸣] = record { _⊚_ = _⊚⸢≼⸢env♯⸣⸣_ }
  Precision[env♯] : ∀ {Γ} → Precision 0ᴸ (env♯ Γ)
  Precision[env♯] = mk[Precision] _≼⸢env♯⸣_

_[_]♯ : ∀ {Γ} → env♯ Γ → var Γ → ⟪ ℤ♯ ⟫
(n♯ ∷ ρ♯) [ Zero ]♯ = n♯
(n♯ ∷ ρ♯) [ Succ x ]♯ = ρ♯ [ x ]♯

_[_↦_]♯ : ∀ {Γ} → env♯ Γ → var Γ → ⟪ ℤ♯ ⟫ → env♯ Γ
(i ∷ ρ) [ Zero ↦ i′ ]♯ = i′ ∷ ρ
(i ∷ ρ) [ Succ x ↦ i′ ]♯ = i ∷ (ρ [ x ↦ i′ ]♯)

η⸢env⸣ : ∀ {Γ} → env Γ → env♯ Γ
η⸢env⸣ [] = []
η⸢env⸣ (n ∷ ρ) = ηᶜ[ ⇄ℤ⇄ ] ⋅ ♮ n ∷ η⸢env⸣ ρ

abstract
  monotonic[η⸢env⸣] : ∀ {Γ} → proper (_⊑_ ⇉ _⊑_) (η⸢env⸣ {Γ})
  monotonic[η⸢env⸣] ↯ = xRx

data _∈γ_ : ∀ {Γ} → env Γ → env♯ Γ → Set where
  [] : [] ∈γ []
  _∷_ : ∀ {Γ} {ρ : env Γ} {ρ♯ : env♯ Γ} {n n♯} → ♮ n ⋿ γᶜ[ ⇄ℤ⇄ ] ⋅ n♯ → ρ ∈γ ρ♯ → (n ∷ ρ) ∈γ (n♯ ∷ ρ♯)

abstract
  monotonic[γ⸢env⸣] : ∀ {Γ} → proper (_⊑_ ⇉ _⊒_ ⇉ [→]) (flip $ _∈γ_ {Γ})
  monotonic[γ⸢env⸣] [] ↯ [] = []
  monotonic[γ⸢env⸣] (n₁⊑n₂ ∷ ρ₁⊑ρ₂) ↯ (n∈γ[n♯] ∷ ρ∈γ[ρ♯]) = res[X][℘]⸢⊑⸣ (res[x][↗]⸢⊑⸣ {f = γᶜ[ ⇄ℤ⇄ ]} n₁⊑n₂) n∈γ[n♯] ∷ monotonic[γ⸢env⸣] ρ₁⊑ρ₂ ↯ ρ∈γ[ρ♯]

sound[ηγ⸢env⸣] : ∀ {Γ} {ρ : env Γ} → ρ ∈γ η⸢env⸣ ρ
sound[ηγ⸢env⸣] {ρ = []} = []
sound[ηγ⸢env⸣] {ρ = x ∷ ρ} = soundᶜ[ ⇄ℤ⇄ ] ∷ sound[ηγ⸢env⸣]

complete[ηγ⸢env⸣] : ∀ {Γ} {ρ : env Γ} {ρ♯} → ρ ∈γ ρ♯ → η⸢env⸣ ρ ⊑ ρ♯
complete[ηγ⸢env⸣] [] = []
complete[ηγ⸢env⸣] (n∈γ[n♯] ∷ ρ∈γ[ρ♯]) = completeᶜ[ ⇄ℤ⇄ ] n∈γ[n♯] ∷ complete[ηγ⸢env⸣] ρ∈γ[ρ♯]

-- Ordered Universe --

⇄env⇄ : ∀ {Γ} → ⇧ (env Γ) ⇄ᶜ ⇧ (env♯ Γ)
⇄env⇄ = mk[⇄ᶜ♭] $ record
  { η = η⸢env⸣
  ; monotonic[η] = monotonic[η⸢env⸣]
  ; γ = flip _∈γ_
  ; monotonic[γ] = monotonic[γ⸢env⸣]
  ; sound = sound[ηγ⸢env⸣]
  ; complete = complete[ηγ⸢env⸣]
  }

lookup♯[_] : ∀ {Γ} → var Γ → ⟪ ⇧ (env♯ Γ) ↗ ℤ♯ ⟫
lookup♯[ x ] = witness (curry⸢λ♭⸣ id⸢λ⸣) $ mk[witness] (λ ρ♯ → ρ♯ [ x ]♯) (ppr {x = x})
  where
    ppr : ∀ {Γ} {x : var Γ} → proper (_⊑_ ⇉ _⊑♮_) (λ ρ♯ → ρ♯ [ x ]♯)
    ppr {x = Zero}  (n₁⊑n₂ ∷ ρ₁⊑ρ₂) = n₁⊑n₂
    ppr {x = Succ x} (n₁⊑n₂ ∷ ρ₁⊑ρ₂) = ppr {x = x} ρ₁⊑ρ₂

extend♯[_] : ∀ {Γ} → var Γ → ⟪ ⇧ (env♯ Γ) ↗ ℤ♯ ↗ ⇧ (env♯ Γ) ⟫
extend♯[ x ] = witness (curry⸢λ♭⸣ $ curry⸢λ⸣ id⸢λ♭⸣) $ mk[witness] (λ ρ♯ i♯ → ρ♯ [ x ↦ i♯ ]♯) (ppr x)
  where
    ppr : ∀ {Γ} (x : var Γ) → proper (_⊑_ ⇉ _⊑♮_ ⇉ _⊑_) (λ ρ♯ i♯ → ρ♯ [ x ↦ i♯ ]♯)
    ppr Zero (⊑ⁱ ∷ ⊑ʳ) ⊑ⁱ′ = ⊑ⁱ′ ∷ ⊑ʳ
    ppr (Succ x) (⊑ⁱ ∷ ⊑ʳ) ⊑ⁱ′ = ⊑ⁱ ∷ ppr x ⊑ʳ ⊑ⁱ′

-- Abstraction --

η[lookup] : ∀ {Γ} {x : var Γ} {ρ : ⟪ ⇧ (env Γ) ⟫} → ηᶜ[ ⇄ℤ⇄ ] ⋅ (lookup♮[ x ] ⋅ ρ) ⊑♮ lookup♯[ x ] ⋅ (ηᶜ[ ⇄env⇄ ] ⋅ ρ)
η[lookup] {x = Zero}  {ρ = ♮⟨ n ∷ ρ ⟩} = xRx
η[lookup] {x = Succ x} {ρ = ♮⟨ n ∷ ρ ⟩} = η[lookup] {x = x} {♮ ρ}

α[lookup] : ∀ {Γ} {x : var Γ} → α[ ⇄env⇄ ↗⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ (pure ⋅ lookup♮[ x ]) ⊑♮ pure ⋅ lookup♯[ x ]
α[lookup] {x = x} = π₂ ηηᶜ[ ⇄env⇄ , ⇄ℤ⇄ ] $ ext[↗]⸢⊑⸣ $ λ {ρ} → η[lookup] {x = x} {ρ}

η[extend] : ∀ {Γ} {x : var Γ} {ρ : ⟪ ⇧ (env Γ) ⟫} {i : ⟪ ⇧ ℤ ⟫} → ηᶜ[ ⇄env⇄ ] ⋅ (extend♮[ x ] ⋅ ρ ⋅ i) ⊑♮ extend♯[ x ] ⋅ (ηᶜ[ ⇄env⇄ ] ⋅ ρ) ⋅ (ηᶜ[ ⇄ℤ⇄ ] ⋅ i)
η[extend] {x = Zero} {ρ = ♮⟨ i ∷ ρ ⟩} {i = ♮⟨ i♭ ⟩} = ♮⟨ xRx ∷ xRx ⟩
η[extend] {x = Succ x} {ρ = ♮⟨ i ∷ ρ ⟩} {i = ♮⟨ i♭ ⟩} = ♮⟨ xRx ∷ elim[⊑♮] (η[extend] {x = x} {♮ ρ} {♮ i♭}) ⟩

α[extend] : ∀ {Γ} {x : var Γ} → α[ (⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄ℤ⇄) ↗⸢⇄ᶜ⸣ ⇄env⇄ ] ⋅ (pure ⋅ (uncurry♮ ⋅ extend♮[ x ])) ⊑♮ pure ⋅ (uncurry♮ ⋅ extend♯[ x ])
α[extend] {x = x} = π₂ ηηᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄ℤ⇄ , ⇄env⇄ ] $ ext[↗]⸢⊑⸣ $ λ { {♮⟨ ⟨ ρ , i ⟩ ⟩} → η[extend] {x = x} {ρ} {i} }
