module Poset.GaloisConnection.Kleisli where

open import Prelude
open import Poset.Poset
open import Poset.Fun
open import Poset.Power
open import Poset.Product
open import Poset.Lib
open import Poset.ProofMode
open import Poset.PowerMonad

open import Poset.GaloisConnection.Classical

infixr 11 _⇄ᵐ_
infixr 11 _↗⸢⇄ᵐ⸣_
infixr 30 _⊚⸢⇄ᵐ⸣_

record _⇄ᵐ_ {ℓ} (A B : Poset ℓ) : Set (↑ᴸ ℓ) where
  field
    αᵐ[_] : ⟪ A ↗ ℘ B ⟫
    γᵐ[_] : ⟪ B ↗ ℘ A ⟫
    extensiveᵐ[_] : return♮ ⊑♮ γᵐ[_] ⟐ αᵐ[_]
    reductiveᵐ[_] : αᵐ[_] ⟐ γᵐ[_] ⊑♮ return♮
open _⇄ᵐ_ public

⟦extensiveᵐ⟧ : ∀ {ℓ} {A B : Poset ℓ} {α : ⟪ A ↗ ℘ B ⟫} {γ : ⟪ B ↗ ℘ A ⟫} → return♮ ⊑♮ γ ⟐ α ↔ (∀ {x} → x ⋿ γ *♮ ⋅ (α ⋅ x))
⟦extensiveᵐ⟧ {A = A} {B} {α} {γ} = ⟨ LHS , RHS ⟩
  where
    LHS : return♮ ⊑♮ γ ⟐ α → ∀ {x} → x ⋿ γ *♮ ⋅ (α ⋅ x)
    LHS expansive = π₁ ⟦return⊑X⟧ $ res[f][↗]⸢⊑⸣ expansive
    RHS : (∀ {x} → x ⋿ γ *♮ ⋅ (α ⋅ x)) → return♮ ⊑♮ γ ⟐ α
    RHS sound = ext[↗]⸢⊑⸣ $ π₂ ⟦return⊑X⟧ sound

⟦reductiveᵐ⟧ : ∀ {ℓ} {A B : Poset ℓ} {α : ⟪ A ↗ ℘ B ⟫} {γ : ⟪ B ↗ ℘ A ⟫} → α ⟐ γ ⊑♮ return♮ ↔ (∀ {x♯ y♯} → y♯ ⋿ α *♮ ⋅ (γ ⋅ x♯) → y♯ ⊑♮ x♯)
⟦reductiveᵐ⟧ {A = A} {B} {α} {γ} = ⟨ LHS , RHS ⟩
  where
    LHS : α ⟐ γ ⊑♮ return♮ → ∀ {x♯ y♯} → y♯ ⋿ α *♮ ⋅ (γ ⋅ x♯) → y♯ ⊑♮ x♯
    LHS contractive x♯∈α[γ[y♯]] = π₁ ⟦return⊑X⟧ $ res[f][↗]⸢⊑⸣ contractive ⊚ π₂ ⟦return⊑X⟧ x♯∈α[γ[y♯]]

    RHS : (∀ {x♯ y♯} → y♯ ⋿ α *♮ ⋅ (γ ⋅ x♯) → y♯ ⊑♮ x♯) → α ⟐ γ ⊑♮ return♮
    RHS complete = ext[↗]⸢⊑⸣ $ ext[℘]⸢⊑⸣ $ complete

soundᵐ[_] : ∀ {ℓ} {A B : Poset ℓ} (A⇄B : A ⇄ᵐ B) → ∀ {x} → x ⋿ γᵐ[ A⇄B ] *♮ ⋅ (αᵐ[ A⇄B ] ⋅ x)
soundᵐ[ A⇄B ] = π₁ ⟦extensiveᵐ⟧ extensiveᵐ[ A⇄B ]

completeᵐ[_] : ∀ {ℓ} {A B : Poset ℓ} (A⇄B : A ⇄ᵐ B) → ∀ {x♯ y♯} → y♯ ⋿ αᵐ[ A⇄B ] *♮ ⋅ (γᵐ[ A⇄B ] ⋅ x♯) → y♯ ⊑♮ x♯
completeᵐ[ A⇄B ] = π₁ ⟦reductiveᵐ⟧ reductiveᵐ[ A⇄B ]

left-unit-extensive[⟐]ᵐ[_] : ∀ {ℓ} {A B₁ B₂ : Poset ℓ} (⇄B⇄ : B₁ ⇄ᵐ B₂) {f : ⟪ A ↗ ℘ B₁ ⟫} → f ⊑♮ (γᵐ[ ⇄B⇄ ] ⟐ αᵐ[ ⇄B⇄ ]) ⟐ f
left-unit-extensive[⟐]ᵐ[ ⇄B⇄ ] {f} = let open ProofMode[⊑] in [proof-mode]
  do [[ f ]]
   ‣ ⟅ ◇ left-unit[⟐] ⟆⸢≈⸣
   ‣ [[ return♮ ⟐ f ]]
   ‣ [focus-left [⟐] 𝑜𝑓 f ] ⟅ extensiveᵐ[ ⇄B⇄ ] ⟆
   ‣ [[ (γᵐ[ ⇄B⇄ ] ⟐ αᵐ[ ⇄B⇄ ]) ⟐ f ]]
   ∎

right-unit-extensive[⟐]ᵐ[_] : ∀ {ℓ} {A₁ A₂ B : Poset ℓ} (⇄A⇄ : A₁ ⇄ᵐ A₂) {f : ⟪ A₁ ↗ ℘ B ⟫} → f ⊑♮ f ⟐ γᵐ[ ⇄A⇄ ] ⟐ αᵐ[ ⇄A⇄ ]
right-unit-extensive[⟐]ᵐ[ ⇄A⇄ ] {f} = let open ProofMode[⊑] in [proof-mode]
  do [[ f ]]
   ‣ ⟅ ◇ right-unit[⟐] ⟆⸢≈⸣
   ‣ [[ f ⟐ return♮ ]]
   ‣ [focus-right [⟐] 𝑜𝑓 f ] ⟅ extensiveᵐ[ ⇄A⇄ ] ⟆
   ‣ [[ f ⟐ γᵐ[ ⇄A⇄ ] ⟐ αᵐ[ ⇄A⇄ ] ]]
   ∎

left-unit-reductive[⟐]ᵐ[_] : ∀ {ℓ} {A B₁ B₂ : Poset ℓ} (⇄B⇄ : B₁ ⇄ᵐ B₂) {f : ⟪ A ↗ ℘ B₂ ⟫} → (αᵐ[ ⇄B⇄ ] ⟐ γᵐ[ ⇄B⇄ ]) ⟐ f ⊑♮ f
left-unit-reductive[⟐]ᵐ[ ⇄B⇄ ] {f} = let open ProofMode[⊑] in [proof-mode]
  do [[ (αᵐ[ ⇄B⇄ ] ⟐ γᵐ[ ⇄B⇄ ]) ⟐ f ]]
   ‣ [focus-left [⟐] 𝑜𝑓 f ] ⟅ reductiveᵐ[ ⇄B⇄ ] ⟆
   ‣ [[ return♮ ⟐ f ]]
   ‣ ⟅ left-unit[⟐] ⟆⸢≈⸣
   ‣ [[ f ]]
   ∎

right-unit-reductive[⟐]ᵐ[_] : ∀ {ℓ} {A₁ A₂ B : Poset ℓ} (⇄A⇄ : A₁ ⇄ᵐ A₂) {f : ⟪ A₂ ↗ ℘ B ⟫} → f ⟐ αᵐ[ ⇄A⇄ ] ⟐ γᵐ[ ⇄A⇄ ] ⊑♮ f
right-unit-reductive[⟐]ᵐ[ ⇄A⇄ ] {f} = let open ProofMode[⊑] in [proof-mode]
  do [[ f ⟐ αᵐ[ ⇄A⇄ ] ⟐ γᵐ[ ⇄A⇄ ] ]]
   ‣ [focus-right [⟐] 𝑜𝑓 f ] ⟅ reductiveᵐ[ ⇄A⇄ ] ⟆
   ‣ [[ f ⟐ return♮ ]]
   ‣ ⟅ right-unit[⟐] ⟆⸢≈⸣
   ‣ [[ f ]]
   ∎

weaken[α]ᵐ : ∀ {ℓ} {A B : Poset ℓ} (A⇄B₁ A⇄B₂ : A ⇄ᵐ B) → γᵐ[ A⇄B₂ ] ⊑♮ γᵐ[ A⇄B₁ ] → αᵐ[ A⇄B₁ ] ⊑♮ αᵐ[ A⇄B₂ ]
weaken[α]ᵐ A⇄B₁ A⇄B₂ γ₂⊑γ₁ = let open ProofMode[⊑] in [proof-mode]
  do [[ αᵐ[ A⇄B₁ ] ]]
   ‣ ⟅ right-unit-extensive[⟐]ᵐ[ A⇄B₂ ] ⟆
   ‣ [[ αᵐ[ A⇄B₁ ] ⟐ γᵐ[ A⇄B₂ ] ⟐ αᵐ[ A⇄B₂ ] ]]
   ‣ [focus-right [⟐] 𝑜𝑓 αᵐ[ A⇄B₁ ] ] $ [focus-left [⟐] 𝑜𝑓 αᵐ[ A⇄B₂ ] ] ⟅ γ₂⊑γ₁ ⟆
   ‣ [[ αᵐ[ A⇄B₁ ] ⟐ γᵐ[ A⇄B₁ ] ⟐ αᵐ[ A⇄B₂ ] ]]
   ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
   ‣ [[ (αᵐ[ A⇄B₁ ] ⟐ γᵐ[ A⇄B₁ ]) ⟐ αᵐ[ A⇄B₂ ] ]]
   ‣ ⟅ left-unit-reductive[⟐]ᵐ[ A⇄B₁ ] ⟆
   ‣ [[ αᵐ[ A⇄B₂ ] ]]
   ∎

unique[α]ᵐ : ∀ {ℓ} {A B : Poset ℓ} (A⇄B₁ A⇄B₂ : A ⇄ᵐ B) → γᵐ[ A⇄B₁ ] ≈♮ γᵐ[ A⇄B₂ ] → αᵐ[ A⇄B₁ ] ≈♮ αᵐ[ A⇄B₂ ]
unique[α]ᵐ A⇄B₁ A⇄B₂ γ₁≈γ₂ = ⋈ᴳ (weaken[α]ᵐ A⇄B₁ A⇄B₂ $ xRxᴳ $ ◇ γ₁≈γ₂) (weaken[α]ᵐ A⇄B₂ A⇄B₁ $ xRxᴳ γ₁≈γ₂)

weaken[γ]ᵐ : ∀ {ℓ} {A B : Poset ℓ} (A⇄B₁ A⇄B₂ : A ⇄ᵐ B) → αᵐ[ A⇄B₂ ] ⊑♮ αᵐ[ A⇄B₁ ] → γᵐ[ A⇄B₁ ] ⊑♮ γᵐ[ A⇄B₂ ]
weaken[γ]ᵐ A⇄B₁ A⇄B₂ α₂⊑α₁ = let open ProofMode[⊑] in [proof-mode]
  do [[ γᵐ[ A⇄B₁ ] ]]
   ‣ ⟅ left-unit-extensive[⟐]ᵐ[ A⇄B₂ ] ⟆
   ‣ [[ (γᵐ[ A⇄B₂ ] ⟐ αᵐ[ A⇄B₂ ]) ⟐ γᵐ[ A⇄B₁ ] ]]
   ‣ [focus-left [⟐] 𝑜𝑓 γᵐ[ A⇄B₁ ] ] $ [focus-right [⟐] 𝑜𝑓 γᵐ[ A⇄B₂ ] ] ⟅ α₂⊑α₁ ⟆
   ‣ [[ (γᵐ[ A⇄B₂ ] ⟐ αᵐ[ A⇄B₁ ]) ⟐ γᵐ[ A⇄B₁ ] ]]
   ‣ ⟅ associative[⟐] ⟆⸢≈⸣
   ‣ [[ γᵐ[ A⇄B₂ ] ⟐ αᵐ[ A⇄B₁ ] ⟐ γᵐ[ A⇄B₁ ] ]]
   ‣ ⟅ right-unit-reductive[⟐]ᵐ[ A⇄B₁ ] ⟆
   ‣ [[ γᵐ[ A⇄B₂ ] ]]
   ∎

unique[γ]ᵐ : ∀ {ℓ} {A B : Poset ℓ} (A⇄B₁ A⇄B₂ : A ⇄ᵐ B) → αᵐ[ A⇄B₁ ] ≈♮ αᵐ[ A⇄B₂ ] → γᵐ[ A⇄B₁ ] ≈♮ γᵐ[ A⇄B₂ ]
unique[γ]ᵐ A⇄B₁ A⇄B₂ α₁≈α₂ = ⋈ᴳ (weaken[γ]ᵐ A⇄B₁ A⇄B₂ $ xRxᴳ $ ◇ α₁≈α₂) (weaken[γ]ᵐ A⇄B₂ A⇄B₁ $ xRxᴳ α₁≈α₂)

_⊚⸢⇄ᵐ⸣_ : ∀ {ℓ} {A B C : Poset ℓ} → B ⇄ᵐ C → A ⇄ᵐ B → A ⇄ᵐ C
B⇄C ⊚⸢⇄ᵐ⸣ A⇄B = record
  { αᵐ[_] = αᵐ[ B⇄C ] ⟐ αᵐ[ A⇄B ]
  ; γᵐ[_] = γᵐ[ A⇄B ] ⟐ γᵐ[ B⇄C ]
  ; extensiveᵐ[_] = let open ProofMode[⊑] in [proof-mode]
      do [[ return♮ ]]
       ‣ ⟅ extensiveᵐ[ A⇄B ] ⟆
       ‣ [[ γᵐ[ A⇄B ] ⟐ αᵐ[ A⇄B ] ]]
       ‣ [focus-left [⟐] 𝑜𝑓 αᵐ[ A⇄B ] ] begin
           do [[ γᵐ[ A⇄B ] ]]
            ‣ ⟅ right-unit-extensive[⟐]ᵐ[ B⇄C ] ⟆
            ‣ [[ γᵐ[ A⇄B ] ⟐ (γᵐ[ B⇄C ] ⟐ αᵐ[ B⇄C ]) ]]
            ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
            ‣ [[ (γᵐ[ A⇄B ] ⟐ γᵐ[ B⇄C ]) ⟐ αᵐ[ B⇄C ] ]]
           end
       ‣ [[ ((γᵐ[ A⇄B ] ⟐ γᵐ[ B⇄C ]) ⟐ αᵐ[ B⇄C ]) ⟐ αᵐ[ A⇄B ] ]]
       ‣ ⟅ associative[⟐] ⟆⸢≈⸣
       ‣ [[ (γᵐ[ A⇄B ] ⟐ γᵐ[ B⇄C ]) ⟐ (αᵐ[ B⇄C ] ⟐ αᵐ[ A⇄B ]) ]]
       ∎
  ; reductiveᵐ[_] = let open ProofMode[⊑] in [proof-mode]
      do [[ (αᵐ[ B⇄C ] ⟐ αᵐ[ A⇄B ]) ⟐ (γᵐ[ A⇄B ] ⟐ γᵐ[ B⇄C ]) ]]
       ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
       ‣ [[ ((αᵐ[ B⇄C ] ⟐ αᵐ[ A⇄B ]) ⟐ γᵐ[ A⇄B ]) ⟐ γᵐ[ B⇄C ] ]]
       ‣ [focus-left [⟐] 𝑜𝑓 γᵐ[ B⇄C ] ] begin
           do [[ (αᵐ[ B⇄C ] ⟐ αᵐ[ A⇄B ]) ⟐ γᵐ[ A⇄B ] ]]
            ‣ ⟅ associative[⟐] ⟆⸢≈⸣
            ‣ [[ αᵐ[ B⇄C ] ⟐ αᵐ[ A⇄B ] ⟐ γᵐ[ A⇄B ] ]]
            ‣ ⟅ right-unit-reductive[⟐]ᵐ[ A⇄B ] ⟆
            ‣ [[ αᵐ[ B⇄C ] ]]
           end
       ‣ [[ αᵐ[ B⇄C ] ⟐ γᵐ[ B⇄C ] ]]
       ‣ ⟅ reductiveᵐ[ B⇄C ] ⟆
       ‣ [[ return♮ ]]
       ∎
  }

_↗⸢⇄ᵐ⸣_ : ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} → A₁ ⇄ᵐ A₂ → B₁ ⇄ᵐ B₂ → (A₁ ↗ ℘ B₁) ⇄ (A₂ ↗ ℘ B₂)
_↗⸢⇄ᵐ⸣_ {A₁ = A₁} {A₂} {B₁} {B₂} ⇄A⇄ ⇄B⇄ = record
  { α[_] = wrap[⟐] ⋅ αᵐ[ ⇄B⇄ ] ⋅ γᵐ[ ⇄A⇄ ]
  ; γ[_] = wrap[⟐] ⋅ γᵐ[ ⇄B⇄ ] ⋅ αᵐ[ ⇄A⇄ ]
  ; extensive[_] = ext[↗]⸢⊑⸣ $ λ {f} → let open ProofMode[⊑] in [proof-mode]
      do [[ f ]]
       ‣ ⟅ left-unit-extensive[⟐]ᵐ[ ⇄B⇄ ] ⟆
       ‣ [[ (γᵐ[ ⇄B⇄ ] ⟐ αᵐ[ ⇄B⇄ ]) ⟐ f ]]
       ‣ ⟅ associative[⟐] ⟆⸢≈⸣
       ‣ [[ γᵐ[ ⇄B⇄ ] ⟐ αᵐ[ ⇄B⇄ ] ⟐ f ]]
       ‣ ⟅ right-unit-extensive[⟐]ᵐ[ ⇄A⇄ ] ⟆
       ‣ [[ (γᵐ[ ⇄B⇄ ] ⟐ αᵐ[ ⇄B⇄ ] ⟐ f) ⟐ γᵐ[ ⇄A⇄ ] ⟐ αᵐ[ ⇄A⇄ ] ]]
       ‣ ⟅ associative[⟐] ⟆⸢≈⸣
       ‣ [[ γᵐ[ ⇄B⇄ ] ⟐ (αᵐ[ ⇄B⇄ ] ⟐ f) ⟐ γᵐ[ ⇄A⇄ ] ⟐ αᵐ[ ⇄A⇄ ] ]]
       ‣ [focus-right [⟐] 𝑜𝑓 γᵐ[ ⇄B⇄ ] ] begin
           do [[ (αᵐ[ ⇄B⇄ ] ⟐ f) ⟐ γᵐ[ ⇄A⇄ ] ⟐ αᵐ[ ⇄A⇄ ] ]]
            ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
            ‣ [[ ((αᵐ[ ⇄B⇄ ] ⟐ f) ⟐ γᵐ[ ⇄A⇄ ]) ⟐ αᵐ[ ⇄A⇄ ] ]]
            ‣ [focus-left [⟐] 𝑜𝑓 αᵐ[ ⇄A⇄ ] ] ⟅ associative[⟐] ⟆⸢≈⸣
            ‣ [[ (αᵐ[ ⇄B⇄ ] ⟐ f ⟐ γᵐ[ ⇄A⇄ ]) ⟐ αᵐ[ ⇄A⇄ ] ]]
           end
       ‣ [[ γᵐ[ ⇄B⇄ ] ⟐ (αᵐ[ ⇄B⇄ ] ⟐ f ⟐ γᵐ[ ⇄A⇄ ]) ⟐ αᵐ[ ⇄A⇄ ] ]]
       ‣ [[ (wrap[⟐] ⋅ γᵐ[ ⇄B⇄ ] ⋅ αᵐ[ ⇄A⇄ ] ∘♮ wrap[⟐] ⋅ αᵐ[ ⇄B⇄ ] ⋅ γᵐ[ ⇄A⇄ ]) ⋅ f ]]
       ∎
  ; reductive[_] = ext[↗]⸢⊑⸣ $ λ {f} → let open ProofMode[⊑] in [proof-mode]
      do [[ (wrap[⟐] ⋅ αᵐ[ ⇄B⇄ ] ⋅ γᵐ[ ⇄A⇄ ] ∘♮ wrap[⟐] ⋅ γᵐ[ ⇄B⇄ ] ⋅ αᵐ[ ⇄A⇄ ]) ⋅ f ]]
       ‣ [[ αᵐ[ ⇄B⇄ ] ⟐ (γᵐ[ ⇄B⇄ ] ⟐ f ⟐ αᵐ[ ⇄A⇄ ]) ⟐ γᵐ[ ⇄A⇄ ] ]]
       ‣ [focus-right [⟐] 𝑜𝑓 αᵐ[ ⇄B⇄ ] ] begin
           do [[ (γᵐ[ ⇄B⇄ ] ⟐ f ⟐ αᵐ[ ⇄A⇄ ]) ⟐ γᵐ[ ⇄A⇄ ] ]]
            ‣ ⟅ associative[⟐] ⟆⸢≈⸣
            ‣ [[ γᵐ[ ⇄B⇄ ] ⟐ (f ⟐ αᵐ[ ⇄A⇄ ]) ⟐ γᵐ[ ⇄A⇄ ] ]]
            ‣ [focus-right [⟐] 𝑜𝑓 γᵐ[ ⇄B⇄ ] ] begin
                do [[ (f ⟐ αᵐ[ ⇄A⇄ ]) ⟐ γᵐ[ ⇄A⇄ ] ]]
                 ‣ ⟅ associative[⟐] ⟆⸢≈⸣
                 ‣ [[ f ⟐ αᵐ[ ⇄A⇄ ] ⟐ γᵐ[ ⇄A⇄ ] ]]
                 ‣ ⟅ right-unit-reductive[⟐]ᵐ[ ⇄A⇄ ] ⟆
                 ‣ [[ f ]]
                end
           end
       ‣ [[ αᵐ[ ⇄B⇄ ] ⟐ γᵐ[ ⇄B⇄ ] ⟐ f ]]
       ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
       ‣ [[ (αᵐ[ ⇄B⇄ ] ⟐ γᵐ[ ⇄B⇄ ]) ⟐ f ]]
       ‣ ⟅ left-unit-reductive[⟐]ᵐ[ ⇄B⇄ ] ⟆
       ‣ [[ f ]]
       ∎
  }

-- infixr 4 _α⇄γᵐ⸢♮⸣_
-- record _α⇄γᵐ⸢♮⸣_ {ℓ} (A B : Set ℓ) {{A-PO : PreOrder ℓ A}} {{B-PO : PreOrder ℓ B}} : Set (↑ᴸ ℓ) where
--   field
--     αᵐ⸢♮⸣ : A → B → Set ℓ
--     monotonic[αᵐ⸢♮⸣] : proper (_⊴_ ⇉ _⊵_ ⇉ [→]) αᵐ⸢♮⸣
--     γᵐ⸢♮⸣ : B → A → Set ℓ
--     monotonic[γᵐ⸢♮⸣] : proper (_⊴_ ⇉ _⊵_ ⇉ [→]) γᵐ⸢♮⸣
--     sound[αγᵐ]⸢♮⸣ : ∀ {x : A} → ∃ x^ 𝑠𝑡 αᵐ⸢♮⸣ x x^ × γᵐ⸢♮⸣ x^ x
--     complete[αγᵐ]⸢♮⸣ : ∀ {x₁^ x₂^ x} → γᵐ⸢♮⸣ x₁^ x → αᵐ⸢♮⸣ x x₂^ → x₂^ ⊴ x₁^
-- 
-- mk[α⇄γᵐ]⸢♮⸣ :
--   ∀ {ℓ} {A B : Set ℓ}
--     {{A-PO : PreOrder ℓ A}} {{A-REX : Reflexive (_⊴_ {A = A})}}
--     {{B-PO : PreOrder ℓ B}} {{B-REX : Reflexive (_⊴_ {A = B})}}
--   → A α⇄γᵐ⸢♮⸣ B → ⇧ A α⇄γᵐ ⇧ B
-- mk[α⇄γᵐ]⸢♮⸣ {A = A} {B} A⇄B = record
--   { αᵐ[_] = α
--   ; γᵐ[_] = γ
--   ; extensiveᵐ[_] = π₂ ⟦extensiveᵐ⟧ $ λ {x} → sound {x}
--   ; reductiveᵐ[_] = π₂ ⟦reductiveᵐ⟧ complete
--   }
--   where
--     open _α⇄γᵐ⸢♮⸣_ A⇄B
--     α : ⟪ ⇧ A ↗ ℘ (⇧ B) ⟫
--     α = witness (curry⸢λ♮⸣ id⸢ω♮⸣) $ mk[witness] αᵐ⸢♮⸣ monotonic[αᵐ⸢♮⸣]
--     γ : ⟪ ⇧ B ↗ ℘ (⇧ A) ⟫
--     γ = witness (curry⸢λ♮⸣ id⸢ω♮⸣) $ mk[witness] γᵐ⸢♮⸣ monotonic[γᵐ⸢♮⸣]
--     sound : ∀ {x} → x ⋿ γ * ⋅ (α ⋅ x)
--     sound {♮⟨ x ⟩} with sound[αγᵐ]⸢♮⸣ {x}
--     ... | ∃ x^ ,, x^∈α[x] , x∈γ[x^]  = ∃℘ ♮ x^ ,, x^∈α[x] ,, x∈γ[x^]
--     complete : ∀ {x^ y^} → x^ ⋿ α * ⋅ (γ ⋅ y^) → x^ ⊑ y^
--     complete (∃℘ x ,, x∈γ[x^] ,, y^∈α[x]) = intro[⊑♭] $ complete[αγᵐ]⸢♮⸣ x∈γ[x^] y^∈α[x]
-- 
-- xRx⸢α⇄γᵐ⸣ : ∀ {ℓ} {A : Poset ℓ} → A α⇄γᵐ A
-- xRx⸢α⇄γᵐ⸣ = record
--   { αᵐ[_] = return
--   ; γᵐ[_] = return
--   ; extensiveᵐ[_] = xRx[] $ ◇ left-unit[⟐]
--   ; reductiveᵐ[_] = xRx[] left-unit[⟐]
--   }
-- 
-- α⇄γᵐ→α⇄γ : ∀ {ℓ} {A B : Poset ℓ} → A α⇄γᵐ B → ℘ A α⇄γ ℘ B
-- α⇄γᵐ→α⇄γ A⇄B = record
--   { α[_] = αᵐ[ A⇄B ] *
--   ; γ[_] = γᵐ[ A⇄B ] *
--   ; extensive[_] = let open ProofMode[⊑] in [proof-mode]
--       do [[ idᵒ ]]
--        ‣ ⟅ ◇ left-unit[*/ext] ⟆⸢≈⸣
--        ‣ [[ return * ]]
--        ‣ [focus-in [*] ] ⟅ extensiveᵐ[ A⇄B ] ⟆
--        ‣ [[ (γᵐ[ A⇄B ] ⟐ αᵐ[ A⇄B ]) * ]]
--        ‣ ⟅ associative[⟐]⸢∘♮⸣ ⟆⸢≈⸣
--        ‣ [[ γᵐ[ A⇄B ] * ∘♮ αᵐ[ A⇄B ] * ]]
--        ∎
--   ; reductive[_] = let open ProofMode[⊑] in [proof-mode]
--       do [[ αᵐ[ A⇄B ] * ∘♮ γᵐ[ A⇄B ] * ]]
--        ‣ ⟅ ◇ associative[⟐]⸢∘♮⸣ ⟆⸢≈⸣
--        ‣ [[ (αᵐ[ A⇄B ] ⟐ γᵐ[ A⇄B ]) * ]]
--        ‣ [focus-in [*] ] ⟅ reductiveᵐ[ A⇄B ] ⟆
--        ‣ [[ return * ]]
--        ‣ ⟅ left-unit[*/ext] ⟆⸢≈⸣
--        ‣ [[ idᵒ ]]
--        ∎
--   }
-- 
-- _×⸢α⇄γᵐ⸣_ : ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} → A₁ α⇄γᵐ B₁ → A₂ α⇄γᵐ B₂ → (A₁ ⟨×⟩ A₂) α⇄γᵐ (B₁ ⟨×⟩ B₂)
-- _×⸢α⇄γᵐ⸣_ {ℓ} {A₁} {A₂} {B₁} {B₂} A₁⇄B₁ A₂⇄B₂ = mk[α⇄γᵐ]⸢♮⸣ $ record
--   { αᵐ⸢♮⸣ = α
--   ; monotonic[αᵐ⸢♮⸣] = monotonic[α]
--   ; γᵐ⸢♮⸣ = γ
--   ; monotonic[γᵐ⸢♮⸣] = monotonic[γ]
--   ; sound[αγᵐ]⸢♮⸣ = sound
--   ; complete[αγᵐ]⸢♮⸣ = complete
--   }
--   where
--     α : prod A₁ A₂ → prod B₁ B₂ → Set ℓ
--     α (x , y) (x^ , y^) = (x^ ⋿ αᵐ[ A₁⇄B₁ ] ⋅ x) × (y^ ⋿ αᵐ[ A₂⇄B₂ ] ⋅ y)
--     abstract
--       monotonic[α] : proper (_⊴_ ⇉ _⊵_ ⇉ [→]) α
--       monotonic[α] (x₁⊑x₂ , y₁⊑y₂) (x₁^⊒x₂^ , y₁^⊒y₂^) (x₁^∈α[x₁] , y₁^∈α[y₁]) =
--           res-X-x[ω]⸢⊑⸣ (res-x[λ]⸢⊑⸣ {f = αᵐ[ A₁⇄B₁ ]} x₁⊑x₂) x₁^⊒x₂^ x₁^∈α[x₁]
--         , res-X-x[ω]⸢⊑⸣ (res-x[λ]⸢⊑⸣ {f = αᵐ[ A₂⇄B₂ ]} y₁⊑y₂) y₁^⊒y₂^ y₁^∈α[y₁]
--     γ : prod B₁ B₂ → prod A₁ A₂ → Set ℓ
--     γ (x^ , y^) (x , y) = (x ⋿ γᵐ[ A₁⇄B₁ ] ⋅ x^) × (y ⋿ γᵐ[ A₂⇄B₂ ] ⋅ y^)
--     abstract
--       monotonic[γ] : proper (_⊴_ ⇉ _⊵_ ⇉ [→]) γ
--       monotonic[γ] (x₁^⊑x₂^ , y₁^⊑y₂^) (x₁⊒x₂ , y₁⊒y₂) (x₁∈γ[x₁^] , y₁∈γ[y₁^]) =
--           res-X-x[ω]⸢⊑⸣ (res-x[λ]⸢⊑⸣ {f = γᵐ[ A₁⇄B₁ ]} x₁^⊑x₂^) x₁⊒x₂ x₁∈γ[x₁^]
--         , res-X-x[ω]⸢⊑⸣ (res-x[λ]⸢⊑⸣ {f = γᵐ[ A₂⇄B₂ ]} y₁^⊑y₂^) y₁⊒y₂ y₁∈γ[y₁^]
--     sound : ∀ {xy : prod A₁ A₂} → ∃ xy^ 𝑠𝑡 α xy xy^ × γ xy^ xy
--     sound {x , y} with soundᵐ[ A₁⇄B₁ ] {x} | soundᵐ[ A₂⇄B₂ ] {y}
--     ... | ∃℘ x^ ,, x^∈α[x] ,, x∈γ[x^] | ∃℘ y^ ,, y∈α[y^] ,, y^∈γ[y] = ∃ (x^ , y^) ,, (x^∈α[x] , y∈α[y^]) , (x∈γ[x^] , y^∈γ[y])
--     complete : ∀ {xy₁^ xy₂^ : prod B₁ B₂} {xy : prod A₁ A₂} → γ xy₁^ xy → α xy xy₂^ → xy₂^ ⊴ xy₁^
--     complete {x₁^ , y₁^} {x₂^ , y₂^} {x , y} (x∈γ[x₁^] , y∈γ[y₁^]) (x₂^∈α[x] , y₂^∈α[y]) =
--         (completeᵐ[ A₁⇄B₁ ] $ ∃℘ x ,, x∈γ[x₁^] ,, x₂^∈α[x])
--       , (completeᵐ[ A₂⇄B₂ ] $ ∃℘ y ,, y∈γ[y₁^] ,, y₂^∈α[y])
