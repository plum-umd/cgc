module CDGAI.BSemanticsAbstract where

open import Prelude
open import Poset
open import CDGAI.ZAbstraction
open import CDGAI.BoolAbstraction
open import CDGAI.EnvAbstraction
open import CDGAI.ASyntax
open import CDGAI.ASemantics
open import CDGAI.ASemanticsAbstract
open import CDGAI.BSyntax
open import CDGAI.BSemantics

⟦_⟧ᵇᶜ♯ : comparison → ⟪ ℤ♯ ↗ ℤ♯ ↗ ⇧ 𝔹♯ ⟫
⟦ [≟] ⟧ᵇᶜ♯ = [⁇ᴮ[≡]♯]
⟦ [⩻] ⟧ᵇᶜ♯ = [⁇ᴮ[<]♯]

_⨹♯_ : 𝔹♯ → 𝔹♯ → 𝔹♯
None ⨹♯ _ = None
_ ⨹♯ None = None
Any ⨹♯ _ = Any
_ ⨹♯ Any = Any
False ⨹♯ b = b
b ⨹♯ False = b
True ⨹♯ True = True

_⨻♯_ : 𝔹♯ → 𝔹♯ → 𝔹♯
None ⨻♯ _ = None
_ ⨻♯ None = None
Any ⨻♯ _ = Any
_ ⨻♯ Any = Any
True ⨻♯ b = b
b ⨻♯ True = b
False ⨻♯ False = False

⟦_⟧ᵇˡ♯ : logical → ⟪ ⇧ 𝔹♯ ↗ ⇧ 𝔹♯ ↗ ⇧ 𝔹♯ ⟫
⟦ [∨] ⟧ᵇˡ♯ = witness (curry⸢λ♭⸣ $ curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] _⨹♯_ P
  where
    P : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) _⨹♯_
    P None ⊑₂ = None
    P Any True = Any
    P Any False = Any
    P Any Any = Any
    P {True} Any None = None
    P {False} Any None = None
    P {None} Any None = None
    P {Any} Any None = None
    P True True = True
    P True False = True
    P True Any = Any
    P True None = None
    P False True = True
    P False False = False
    P False Any = Any
    P False None = None

⟦ [∧] ⟧ᵇˡ♯ = witness (curry⸢λ♭⸣ $ curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] _⨻♯_ P
  where
    P : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) _⨻♯_
    P None ⊑₂ = None
    P Any True = Any
    P Any False = Any
    P Any Any = Any
    P {True} Any None = None
    P {False} Any None = None
    P {None} Any None = None
    P {Any} Any None = None
    P True True = True
    P True False = False
    P True Any = Any
    P True None = None
    P False True = False
    P False False = False
    P False Any = Any
    P False None = None

⟦_⟧ᵇ♯ : ∀ {Γ} → bexp Γ → ⟪ ⇧ (env♯ Γ) ↗ ⇧ 𝔹♯ ⟫
⟦ be ⟧ᵇ♯ = witness (curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] (F be) (P be)
  where
    F : ∀ {Γ} → bexp Γ → env♯ Γ → 𝔹♯
    F True ρ♯ = True
    F False ρ♯ = False
    F (Compare[ o ] ae₁ ae₂) ρ♯ = ♭ (⟦ o ⟧ᵇᶜ♯ ⋅ (⟦ ae₁ ⟧ᵃ♯ ⋅ ♮⟨ ρ♯ ⟩) ⋅ (⟦ ae₂ ⟧ᵃ♯ ⋅ ♮⟨ ρ♯ ⟩))
    F (Logical[ o ] be₁ be₂) ρ♯ = ♭ (⟦ o ⟧ᵇˡ♯ ⋅ (⟦ be₁ ⟧ᵇ♯ ⋅ ♮⟨ ρ♯ ⟩) ⋅ (⟦ be₂ ⟧ᵇ♯ ⋅ ♮⟨ ρ♯ ⟩))
    P : ∀ {Γ} (b : bexp Γ) → proper (_⊑_ ⇉ _⊑_) (F b)
    P True ⊑₁ = True
    P False ⊑₁ = False
    P (Compare[ o ] ae₁ ae₂) {ρ₁♯} {ρ₂♯} ⊑₁ = elim[⊑♭] let open ProofMode[⊑] in [proof-mode]
      do [[ ⟦ o ⟧ᵇᶜ♯ ⋅ (⟦ ae₁ ⟧ᵃ♯ ⋅ ♮⟨ ρ₁♯ ⟩) ⋅ (⟦ ae₂ ⟧ᵃ♯ ⋅ ♮⟨ ρ₁♯ ⟩) ]]
       ‣ [focus-left [⋅] 𝑜𝑓 (⟦ ae₂ ⟧ᵃ♯ ⋅ ♮⟨ ρ₁♯ ⟩) ] $ [focus-right [⋅] 𝑜𝑓 ⟦ o ⟧ᵇᶜ♯ ] $ [focus-right [⋅] 𝑜𝑓 ⟦ ae₁ ⟧ᵃ♯ ] ⟅ intro[⊑♮] ⊑₁ ⟆
       ‣ [focus-right [⋅] 𝑜𝑓 ⟦ o ⟧ᵇᶜ♯ ⋅ (⟦ ae₁ ⟧ᵃ♯ ⋅ ♮⟨ ρ₂♯ ⟩) ] $ [focus-right [⋅] 𝑜𝑓 ⟦ ae₂ ⟧ᵃ♯ ] ⟅ intro[⊑♮] ⊑₁ ⟆
       ‣ [[ ⟦ o ⟧ᵇᶜ♯ ⋅ (⟦ ae₁ ⟧ᵃ♯ ⋅ ♮⟨ ρ₂♯ ⟩) ⋅ (⟦ ae₂ ⟧ᵃ♯ ⋅ ♮⟨ ρ₂♯ ⟩) ]]
       ∎
    P (Logical[ o ] be₁ be₂) {ρ₁♯} {ρ₂♯} ⊑₁ = elim[⊑♭] let open ProofMode[⊑] in [proof-mode]
      do [[ ⟦ o ⟧ᵇˡ♯ ⋅ (⟦ be₁ ⟧ᵇ♯ ⋅ ♮⟨ ρ₁♯ ⟩) ⋅ (⟦ be₂ ⟧ᵇ♯ ⋅ ♮⟨ ρ₁♯ ⟩) ]]
       ‣ [focus-left [⋅] 𝑜𝑓 (⟦ be₂ ⟧ᵇ♯ ⋅ ♮⟨ ρ₁♯ ⟩) ] $ [focus-right [⋅] 𝑜𝑓 ⟦ o ⟧ᵇˡ♯ ] $ [focus-right [⋅] 𝑜𝑓 ⟦ be₁ ⟧ᵇ♯ ] ⟅ intro[⊑♮] ⊑₁ ⟆
       ‣ [focus-right [⋅] 𝑜𝑓 ⟦ o ⟧ᵇˡ♯ ⋅ (⟦ be₁ ⟧ᵇ♯ ⋅ ♮⟨ ρ₂♯ ⟩) ] $ [focus-right [⋅] 𝑜𝑓 ⟦ be₂ ⟧ᵇ♯ ] ⟅ intro[⊑♮] ⊑₁ ⟆
       ‣ [[ ⟦ o ⟧ᵇˡ♯ ⋅ (⟦ be₁ ⟧ᵇ♯ ⋅ ♮⟨ ρ₂♯ ⟩) ⋅ (⟦ be₂ ⟧ᵇ♯ ⋅ ♮⟨ ρ₂♯ ⟩) ]]
       ∎

postulate
  α[⟦⟧ᵇ] : ∀ {Γ} (be : bexp Γ) → α[ ⇄env⇄ ↗⸢⇄ᶜ⸣ ⇄𝔹⇄ ] ⋅ ⟦ be ⟧ᵇ ⊑♮ pure ⋅ ⟦ be ⟧ᵇ♯
