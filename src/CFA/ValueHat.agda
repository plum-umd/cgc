module CFA.ValueHat where

open import Prelude
open import POSet

open import CFA.Syntax
open import CFA.Semantics

data value^ Γ : Set where
  FClo      : var Γ → var Γ → call Γ → value^ Γ
  KClo      : var Γ → call Γ → value^ Γ
  Stop      : value^ Γ
  Undefined : value^ Γ

instance
  PreOrder⸢value^⸣ : ∀ {Γ} → PreOrder zeroˡ (value^ Γ)
  PreOrder⸢value^⸣ = ≡-PreOrder

α⸢val⸣ : ∀ {Γ} → value Γ → value^ Γ
α⸢val⸣ (FClo x k c _) = FClo x k c
α⸢val⸣ (KClo x c _)   = KClo x c
α⸢val⸣ Stop           = Stop
α⸢val⸣ Undefined      = Undefined

monotonic[α⸢val⸣] : ∀ {Γ} → proper (_⊴_ ⇉ _⊴_) (α⸢val⸣ {Γ})
monotonic[α⸢val⸣] ↯ = ↯

data γ⸢val⸣ {Γ} : value^ Γ → value Γ → Set where
  FClo      : ∀ {ρ x k c} → γ⸢val⸣ (FClo x k c) (FClo x k c ρ)
  KClo      : ∀ {ρ x c}   → γ⸢val⸣ (KClo x c)   (KClo x c ρ)
  Stop      : γ⸢val⸣ Stop Stop
  Undefined : γ⸢val⸣ Undefined Undefined

monotonic[γ⸢val⸣] : ∀ {Γ} → proper (_⊴_ ⇉ _⊵_ ⇉ [→]) (γ⸢val⸣ {Γ})
monotonic[γ⸢val⸣] ↯ ↯ = id

αγ-sound⸢val⸣ : ∀ {Γ} (v : value Γ) → γ⸢val⸣ (α⸢val⸣ v) v
αγ-sound⸢val⸣ (FClo x k c ρ) = FClo
αγ-sound⸢val⸣ (KClo x c ρ)   = KClo
αγ-sound⸢val⸣ Stop           = Stop
αγ-sound⸢val⸣ Undefined      = Undefined

αγ-complete⸢val⸣ : ∀ {Γ} {v : value Γ} {v^ : value^ Γ} → γ⸢val⸣ v^ v → α⸢val⸣ v ≡ v^
αγ-complete⸢val⸣ FClo = ↯
αγ-complete⸢val⸣ KClo = ↯
αγ-complete⸢val⸣ Stop = ↯
αγ-complete⸢val⸣ Undefined = ↯

⇄val⇄ : ∀ {Γ} → ⇧ (value Γ) ⇄ᶜ ⇧ (value^ Γ)
⇄val⇄ = mk[η⇄γ]⸢↑⸣ $ record
  { η = α⸢val⸣
  ; monotonic[η] = monotonic[α⸢val⸣]
  ; γ = γ⸢val⸣
  ; monotonic[γ] = monotonic[γ⸢val⸣]
  ; sound = λ {x} → αγ-sound⸢val⸣ x
  ; complete = αγ-complete⸢val⸣
  }
