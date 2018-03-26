module Poset.GaloisConnection.Constructive where

open import Prelude
open import Poset.Poset
open import Poset.Fun
open import Poset.Power
open import Poset.Product
open import Poset.ProofMode
open import Poset.Lib
open import Poset.PowerMonad
open import Poset.Option

open import Poset.GaloisConnection.Classical
open import Poset.GaloisConnection.Kleisli

infixr 11 _⇄ᶜ_
-- infixr 11 _⇄ᶜ♭_

record _⇄ᶜ_ {ℓ} (A B : Poset ℓ) : Set (↑ᴸ ℓ) where
  field
    ηᶜ[_] : ⟪ A ↗ B ⟫
    γᶜ[_] : ⟪ B ↗ ℘ A ⟫
    extensiveᶜ[_] : return♮ ⊑♮ γᶜ[_] ⟐ pure ⋅ ηᶜ[_]
    reductiveᶜ[_] : pure ⋅ ηᶜ[_] ⟐ γᶜ[_] ⊑♮ return♮
open _⇄ᶜ_ public

αᶜ[_] : ∀ {ℓ} {A B : Poset ℓ} (A⇄B : A ⇄ᶜ B) → ⟪ A ↗ ℘ B ⟫
αᶜ[ A⇄B ] = pure ⋅ ηᶜ[ A⇄B ]

extensiveᶜ[*][_] : ∀ {ℓ} {A B : Poset ℓ} (⇄A⇄ : A ⇄ᶜ B) {x : ⟪ A ⟫} → return♮ ⋅ x ⊑♮ γᶜ[ ⇄A⇄ ] *♮ ⋅ (αᶜ[ ⇄A⇄ ] ⋅ x)
extensiveᶜ[*][ ⇄A⇄ ] {x} = res[f][↗]⸢⊑⸣ extensiveᶜ[ ⇄A⇄ ]

reductiveᶜ[*][_] : ∀ {ℓ} {A B : Poset ℓ} (⇄A⇄ : A ⇄ᶜ B) {y : ⟪ B ⟫} → αᶜ[ ⇄A⇄ ] *♮ ⋅ (γᶜ[ ⇄A⇄ ] ⋅ y) ⊑♮ return♮ ⋅ y
reductiveᶜ[*][ ⇄A⇄ ] = res[f][↗]⸢⊑⸣ reductiveᶜ[ ⇄A⇄ ]

extensiveᶜ[∘♮][_] : ∀ {ℓ} {A B : Poset ℓ} (⇄A⇄ : A ⇄ᶜ B) → id♮ ⊑♮ γᶜ[ ⇄A⇄ ] *♮ ∘♮ αᶜ[ ⇄A⇄ ] *♮
extensiveᶜ[∘♮][ ⇄A⇄ ] = let open ProofMode[⊑] in [proof-mode]
  do [[ id♮ ]]
   ‣ ⟅ ◇ left-unit[*/ext] ⟆⸢≈⸣
   ‣ [[ return♮ *♮ ]]
   ‣ [focus-in [*] ] begin
       do [[ return♮ ]]
        ‣ ⟅ extensiveᶜ[ ⇄A⇄ ] ⟆
        ‣ [[ γᶜ[ ⇄A⇄ ] ⟐ αᶜ[ ⇄A⇄ ] ]]
       end
   ‣ [[ (γᶜ[ ⇄A⇄ ] ⟐ αᶜ[ ⇄A⇄ ]) *♮ ]]
   ‣ ⟅ associative[*/ext] ⟆⸢≈⸣
   ‣ [[ γᶜ[ ⇄A⇄ ] *♮ ∘♮ αᶜ[ ⇄A⇄ ] *♮ ]]
   ∎

reductiveᶜ[∘♮][_] : ∀ {ℓ} {A B : Poset ℓ} (⇄A⇄ : A ⇄ᶜ B) → αᶜ[ ⇄A⇄ ] *♮ ∘♮ γᶜ[ ⇄A⇄ ] *♮ ⊑♮ id♮
reductiveᶜ[∘♮][ ⇄A⇄ ] = let open ProofMode[⊑] in [proof-mode]
  do [[ αᶜ[ ⇄A⇄ ] *♮ ∘♮ γᶜ[ ⇄A⇄ ] *♮ ]]
   ‣ ⟅ ◇ associative[*/ext] ⟆⸢≈⸣
   ‣ [[ (αᶜ[ ⇄A⇄ ] *♮ ∘♮ γᶜ[ ⇄A⇄ ]) *♮ ]]
   ‣ [focus-in [*] ] begin
       do [[ αᶜ[ ⇄A⇄ ] *♮ ∘♮ γᶜ[ ⇄A⇄ ] ]]
        ‣ ⟅ reductiveᶜ[ ⇄A⇄ ] ⟆
        ‣ [[ return♮ ]]
       end
   ‣ [[ return♮ *♮ ]]
   ‣ ⟅ left-unit[*/ext] ⟆⸢≈⸣
   ‣ [[ id♮ ]]
   ∎

extensiveᶜ[⋅][_] : ∀ {ℓ} {A B : Poset ℓ} (⇄A⇄ : A ⇄ᶜ B) {X : ⟪ ℘ A ⟫} → X ⊑♮ γᶜ[ ⇄A⇄ ] *♮ ⋅ (αᶜ[ ⇄A⇄ ] *♮ ⋅ X)
extensiveᶜ[⋅][ ⇄A⇄ ] = res[f][↗]⸢⊑⸣ extensiveᶜ[∘♮][ ⇄A⇄ ]

reductiveᶜ[⋅][_] : ∀ {ℓ} {A B : Poset ℓ} (⇄A⇄ : A ⇄ᶜ B) {Y : ⟪ ℘ B ⟫} → αᶜ[ ⇄A⇄ ] *♮ ⋅ (γᶜ[ ⇄A⇄ ] *♮ ⋅ Y) ⊑♮ Y
reductiveᶜ[⋅][ ⇄A⇄ ] = res[f][↗]⸢⊑⸣ reductiveᶜ[∘♮][ ⇄A⇄ ]

⟦extensiveᶜ⟧ : ∀ {ℓ} {A B : Poset ℓ} {η : ⟪ A ↗ B ⟫} {γ : ⟪ B ↗ ℘ A ⟫} → return♮ ⊑♮ γ ⟐ pure ⋅ η ↔ (∀ {x} → x ⋿ γ ⋅ (η ⋅ x))
⟦extensiveᶜ⟧ {A = A} {B} {η} {γ} = ⟨ LHS , RHS ⟩
  where
    LHS : return♮ ⊑♮ γ ⟐ pure ⋅ η → ∀ {x} → x ⋿ γ ⋅ (η ⋅ x)
    LHS expansive = π₁ ⟦return⊑X⟧ $ res[f][↗]⸢⊑⸣ $ xRxᴳ right-unit[⟐/pure] ⊚ expansive
    RHS : (∀ {x} → x ⋿ γ ⋅ (η ⋅ x)) → return♮ ⊑♮ γ ⟐ pure ⋅ η
    RHS sound = xRx[≈]⸢⊑♮⸣ (◇ right-unit[⟐/pure]) ⊚ ext[↗]⸢⊑⸣ (π₂ ⟦return⊑X⟧ sound)

⟦reductiveᶜ⟧ : ∀ {ℓ} {A B : Poset ℓ} {η : ⟪ A ↗ B ⟫} {γ : ⟪ B ↗ ℘ A ⟫} → pure ⋅ η ⟐ γ ⊑♮ return♮ ↔ (∀ {x♯ x} → x ⋿ γ ⋅ x♯ → η ⋅ x ⊑♮ x♯)
⟦reductiveᶜ⟧ {A = A} {B} {η} {γ} = ⟨ LHS , RHS ⟩
  where
    LHS : pure ⋅ η ⟐ γ ⊑♮ return♮ → ∀ {x♯ x} → x ⋿ γ ⋅ x♯ → η ⋅ x ⊑♮ x♯
    LHS contractive {x♯} {x} x∈γ[x♯] = π₁ ⟦return⊑X⟧ $ res[f][↗]⸢⊑⸣ contractive ⊚ let open ProofMode[⊑] in [proof-mode]
      do [[ (pure ⋅ η) ⋅ x ]]
       ‣ ⟅ ◇ right-unit[*] ⟆⸢≈⸣
       ‣ [[ (pure ⋅ η) *♮ ⋅ (return♮ ⋅ x) ]]
       ‣ [focus-right [⋅] 𝑜𝑓 (pure ⋅ η) *♮ ] ⟅ π₂ ⟦return⊑X⟧ x∈γ[x♯] ⟆
       ‣ [[ (pure ⋅ η) *♮ ⋅ (γ ⋅ x♯) ]]
       ∎
    RHS : (∀ {x♯ x} → x ⋿ γ ⋅ x♯ → η ⋅ x ⊑♮ x♯) → pure ⋅ η ⟐ γ ⊑♮ return♮
    RHS complete = ext[↗]⸢⊑⸣ $ ext[℘]⸢⊑⸣ H
      where
        H : ∀ {x♯ y♯} → y♯ ⋿ (pure ⋅ η) *♮ ⋅ (γ ⋅ x♯) → y♯ ⊑♮ x♯
        H (∃℘ x ,, x∈γ[x♯] ,, y♯⊑η[x]) = complete x∈γ[x♯] ⊚ y♯⊑η[x]

soundᶜ[_] : ∀ {ℓ} {A B : Poset ℓ} (A⇄B : A ⇄ᶜ B) → ∀ {x} → x ⋿ γᶜ[ A⇄B ] ⋅ (ηᶜ[ A⇄B ] ⋅ x)
soundᶜ[ A⇄B ] = π₁ ⟦extensiveᶜ⟧ extensiveᶜ[ A⇄B ]

completeᶜ[_] : ∀ {ℓ} {A B : Poset ℓ} (A⇄B : A ⇄ᶜ B) → ∀ {x♯ x} → x ⋿ γᶜ[ A⇄B ] ⋅ x♯ → ηᶜ[ A⇄B ] ⋅ x ⊑♮ x♯
completeᶜ[ A⇄B ] = π₁ ⟦reductiveᶜ⟧ reductiveᶜ[ A⇄B ]

left-unit-extensive[⟐]ᶜ[_] : ∀ {ℓ} {A B₁ B₂ : Poset ℓ} (⇄B⇄ : B₁ ⇄ᶜ B₂) {f : ⟪ A ↗ ℘ B₁ ⟫} → f ⊑♮ (γᶜ[ ⇄B⇄ ] ⟐ αᶜ[ ⇄B⇄ ]) ⟐ f
left-unit-extensive[⟐]ᶜ[ ⇄B⇄ ] {f} = let open ProofMode[⊑] in [proof-mode]
  do [[ f ]]
   ‣ ⟅ ◇ left-unit[⟐] ⟆⸢≈⸣
   ‣ [[ return♮ ⟐ f ]]
   ‣ [focus-left [⟐] 𝑜𝑓 f ] ⟅ extensiveᶜ[ ⇄B⇄ ] ⟆
   ‣ [[ (γᶜ[ ⇄B⇄ ] ⟐ αᶜ[ ⇄B⇄ ]) ⟐ f ]]
   ∎

right-unit-extensive[⟐]ᶜ[_] : ∀ {ℓ} {A₁ A₂ B : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) {f : ⟪ A₁ ↗ ℘ B ⟫} → f ⊑♮ f ⟐ γᶜ[ ⇄A⇄ ] ⟐ αᶜ[ ⇄A⇄ ]
right-unit-extensive[⟐]ᶜ[ ⇄A⇄ ] {f} = let open ProofMode[⊑] in [proof-mode]
  do [[ f ]]
   ‣ ⟅ ◇ right-unit[⟐] ⟆⸢≈⸣
   ‣ [[ f ⟐ return♮ ]]
   ‣ [focus-right [⟐] 𝑜𝑓 f ] ⟅ extensiveᶜ[ ⇄A⇄ ] ⟆
   ‣ [[ f ⟐ γᶜ[ ⇄A⇄ ] ⟐ αᶜ[ ⇄A⇄ ] ]]
   ∎

left-unit-reductive[⟐]ᶜ[_] : ∀ {ℓ} {A B₁ B₂ : Poset ℓ} (⇄B⇄ : B₁ ⇄ᶜ B₂) {f : ⟪ A ↗ ℘ B₂ ⟫} → (αᶜ[ ⇄B⇄ ] ⟐ γᶜ[ ⇄B⇄ ]) ⟐ f ⊑♮ f
left-unit-reductive[⟐]ᶜ[ ⇄B⇄ ] {f} = let open ProofMode[⊑] in [proof-mode]
  do [[ (αᶜ[ ⇄B⇄ ] ⟐ γᶜ[ ⇄B⇄ ]) ⟐ f ]]
   ‣ [focus-left [⟐] 𝑜𝑓 f ] ⟅ reductiveᶜ[ ⇄B⇄ ] ⟆
   ‣ [[ return♮ ⟐ f ]]
   ‣ ⟅ left-unit[⟐] ⟆⸢≈⸣
   ‣ [[ f ]]
   ∎

right-unit-reductive[⟐]ᶜ[_] : ∀ {ℓ} {A₁ A₂ B : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) {f : ⟪ A₂ ↗ ℘ B ⟫} → f ⟐ αᶜ[ ⇄A⇄ ] ⟐ γᶜ[ ⇄A⇄ ] ⊑♮ f
right-unit-reductive[⟐]ᶜ[ ⇄A⇄ ] {f} = let open ProofMode[⊑] in [proof-mode]
  do [[ f ⟐ αᶜ[ ⇄A⇄ ] ⟐ γᶜ[ ⇄A⇄ ] ]]
   ‣ [focus-right [⟐] 𝑜𝑓 f ] ⟅ reductiveᶜ[ ⇄A⇄ ] ⟆
   ‣ [[ f ⟐ return♮ ]]
   ‣ ⟅ right-unit[⟐] ⟆⸢≈⸣
   ‣ [[ f ]]
   ∎

-- left-unit-reductive[*]ᶜ[_] : ∀ {ℓ} {A₁ A₂ B : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) {f : ⟪ A₂ ↗ ℘ B ⟫} {X : ⟪ ℘ A₂ ⟫} → f * ⋅ (αᶜ[ ⇄A⇄ ] * ⋅ (γᶜ[ ⇄A⇄ ] * ⋅ X)) ⊑ f * ⋅ X
-- left-unit-reductive[*]ᶜ[ ⇄A⇄ ] {f} {x} = res[f]⸢⊑↗⸣ let open ProofMode[⊑] in [proof-mode]
--   do [[ f * ∘♮ αᶜ[ ⇄A⇄ ] * ∘♮ γᶜ[ ⇄A⇄ ] * ]]
--    ‣ [focus-right [∘♮] 𝑜𝑓 f * ] begin
--        do [[ αᶜ[ ⇄A⇄ ] * ∘♮ γᶜ[ ⇄A⇄ ] * ]]
--         ‣ ⟅ ◇ associative[*/ext] ⟆⸢≈⸣
--         ‣ [[ (αᶜ[ ⇄A⇄ ] * ∘♮ γᶜ[ ⇄A⇄ ]) * ]]
--         ‣ [focus-in [*] ] begin
--             do [[ αᶜ[ ⇄A⇄ ] * ∘♮ γᶜ[ ⇄A⇄ ] ]]
--              ‣ [[ αᶜ[ ⇄A⇄ ] ⟐ γᶜ[ ⇄A⇄ ] ]]
--              ‣ ⟅ reductiveᶜ[ ⇄A⇄ ] ⟆
--              ‣ [[ return ]]
--             end
--         ‣ [[ return * ]]
--         ‣ ⟅ left-unit[*/ext] ⟆⸢≈⸣
--         ‣ [[ id♮ ]]
--        end
--    ‣ [[ f * ∘♮ id♮ ]]
--    ‣ ⟅ right-unit[∘♮] ⟆⸢≈⸣
--    ‣ [[ f * ]]
--   ∎

record _⇄ᶜ♭_ {ℓ} (A B : Set ℓ) {{A-PO : Precision ℓ A}} {{B-PO : Precision ℓ B}} : Set (↑ᴸ ℓ) where
  field
    η : A → B
    monotonic[η] : proper (_⊑_ ⇉ _⊑_) η
    γ : B → A → Set ℓ
    monotonic[γ] : proper (_⊑_ ⇉ _⊒_ ⇉ [→]) γ
    sound : ∀ {x : A} → γ (η x) x
    complete : ∀ {x x♯} → γ x♯ x → η x ⊑ x♯
    
mk[⇄ᶜ♭] :
  ∀ {ℓ} {A B : Set ℓ}
    {{A-PO : Precision ℓ A}} {{A-REX : Reflexive (_⊑_ {A = A})}}
    {{B-PO : Precision ℓ B}} {{B-REX : Reflexive (_⊑_ {A = B})}}
  → A ⇄ᶜ♭ B → ⇧ A ⇄ᶜ ⇧ B
mk[⇄ᶜ♭] {A = A} {B} A⇄B = record
  { ηᶜ[_] = witness (curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] η monotonic[η]
  ; γᶜ[_] = witness (curry⸢λ♭⸣ id⸢ω♭⸣) $ mk[witness] γ monotonic[γ]
  ; extensiveᶜ[_] = π₂ ⟦extensiveᶜ⟧ sound
  ; reductiveᶜ[_] = π₂ ⟦reductiveᶜ⟧ (intro[⊑♭] ∘ complete)
  }
  where open _⇄ᶜ♭_ A⇄B

⇄ᶜ↔⇄ᵐ : ∀ {ℓ} {A B : Poset ℓ} → (A ⇄ᶜ B) ↔ (A ⇄ᵐ B)
⇄ᶜ↔⇄ᵐ = ⟨ LHS , RHS ⟩
  where
    LHS : ∀ {ℓ} {A B : Poset ℓ} → A ⇄ᶜ B → A ⇄ᵐ B
    LHS A⇄B = record
      { αᵐ[_] = αᶜ[ A⇄B ]
      ; γᵐ[_] = γᶜ[ A⇄B ]
      ; extensiveᵐ[_] = extensiveᶜ[ A⇄B ]
      ; reductiveᵐ[_] = reductiveᶜ[ A⇄B ]
      }
    RHS : ∀ {ℓ} {A B : Poset ℓ} → A ⇄ᵐ B → A ⇄ᶜ B
    RHS {A = A} {B} A⇄B = record
      { ηᶜ[_] = η
      ; γᶜ[_] = γᵐ[ A⇄B ]
      ; extensiveᶜ[_] = π₂ ⟦extensiveᶜ⟧ sound
      ; reductiveᶜ[_] = π₂ ⟦reductiveᶜ⟧ complete
      }
      where
        fun : ⟪ A ⟫ → ⟪ B ⟫
        fun x with soundᵐ[ A⇄B ] {x}
        ... | ∃℘ y ,, y∈α[x] ,, x∈γ[y] = y
        abstract
          ppr : proper (_⊑♮_ ⇉ _⊑♮_) fun
          ppr {x} {y} x⊑y with soundᵐ[ A⇄B ] {x} | soundᵐ[ A⇄B ] {y}
          ... | ∃℘ x♯ ,, x♯∈α[x] ,, x∈γ[x♯] | ∃℘ y♯ ,, y♯∈α[y] ,, y∈γ[y♯] =
            res[X][℘]⸢⊑⸣ (res[f][↗]⸢⊑⸣ $ reductiveᵐ[ A⇄B ]) $
            ∃℘ x ,, res[x][℘]⸢⊑⸣ {X = γᵐ[ A⇄B ] ⋅ y♯} x⊑y y∈γ[y♯] ,, x♯∈α[x]
        η : ⟪ A ↗ B ⟫
        η = witness (curry⸢λ⸣ $ id⸢λ⸣) $ mk[witness] fun ppr
        sound : ∀ {x} → x ⋿ γᵐ[ A⇄B ] ⋅ (η ⋅ x)
        sound {x} with soundᵐ[ A⇄B ] {x}
        ... | ∃℘ x♯ ,, x♯∈α[x] ,, x∈γ[x♯] = x∈γ[x♯]
        complete : ∀ {x x♯} → x ⋿ γᵐ[ A⇄B ] ⋅ x♯ → η ⋅ x ⊑♮ x♯
        complete {x} {x♯} x∈γ[x♯] with soundᵐ[ A⇄B ] {x}
        ... | ∃℘ y♯ ,, y♯∈α[x] ,, x∈γ[y♯] = completeᵐ[ A⇄B ] $ ∃℘ x ,, x∈γ[x♯] ,, y♯∈α[x]

⇄ᵐ→⇄ᶜ[_] : ∀ {ℓ} {A B : Poset ℓ} → A ⇄ᵐ B → A ⇄ᶜ B
⇄ᵐ→⇄ᶜ[_] = π₂ ⇄ᶜ↔⇄ᵐ

⇄ᶜ→⇄ᵐ[_] : ∀ {ℓ} {A B : Poset ℓ} → A ⇄ᶜ B → A ⇄ᵐ B
⇄ᶜ→⇄ᵐ[_] = π₁ ⇄ᶜ↔⇄ᵐ

α≈pure[η] : ∀ {ℓ} {A B : Poset ℓ} (A⇄B : A ⇄ᵐ B) → αᵐ[ A⇄B ] ≈♮ αᶜ[ ⇄ᵐ→⇄ᶜ[ A⇄B ] ]
α≈pure[η] A⇄B = unique[α]ᵐ A⇄B ⇄ᶜ→⇄ᵐ[ ⇄ᵐ→⇄ᶜ[ A⇄B ] ] xRx

pure[η]≈α : ∀ {ℓ} {A B : Poset ℓ} (A⇄B : A ⇄ᶜ B) → αᶜ[ A⇄B ] ≈♮ αᵐ[ ⇄ᶜ→⇄ᵐ[ A⇄B ] ]
pure[η]≈α A⇄B = unique[α]ᵐ ⇄ᶜ→⇄ᵐ[ A⇄B ] ⇄ᶜ→⇄ᵐ[ A⇄B ] xRx

module _ {ℓ} {A : Poset ℓ} where
  id⸢⇄ᶜ⸣ : A ⇄ᶜ A
  id⸢⇄ᶜ⸣ = record
    { ηᶜ[_] = id♮
    ; γᶜ[_] = return♮
    ; extensiveᶜ[_] = ext[↗]⸢⊑⸣ $ λ {x} → let open ProofMode[⊑] in [proof-mode]
      do [[ return♮ ⋅ x ]]
       ‣ ⟅ ◇ right-unit[*] ⟆⸢≈⸣
       ‣ [[ return♮ *♮ ⋅ (return♮ ⋅ x) ]]
       ‣ [[ (return♮ ⟐ pure ⋅ id♮) ⋅ x ]]
       ∎
    ; reductiveᶜ[_] = ext[↗]⸢⊑⸣ $ λ {x} → let open ProofMode[⊑] in [proof-mode]
      do [[ (pure ⋅ id♮ ⟐ return♮) ⋅ x ]]
       ‣ ⟅ right-unit[*] ⟆⸢≈⸣
       ‣ [[ pure ⋅ id♮ ⋅ x ]]
       ‣ [[ return♮ ⋅ x ]]
       ∎
    }

_⊚⸢⇄ᶜ⸣_ : ∀ {ℓ} {A B C : Poset ℓ} → B ⇄ᶜ C → A ⇄ᶜ B → A ⇄ᶜ C
_⊚⸢⇄ᶜ⸣_ {ℓ} {A₁} {A₂} {A₃} B⇄C A⇄B = record
  { ηᶜ[_] = ηᶜ[ B⇄C ] ∘♮ ηᶜ[ A⇄B ]
  ; γᶜ[_] = γᶜ[ A⇄B ] ⟐ γᶜ[ B⇄C ]
  ; extensiveᶜ[_] = let open ProofMode[⊑] in [proof-mode]
      do [[ return♮ ]]
       ‣ ⟅ extensiveᵐ[ ⇄ᶜ→⇄ᵐ[ B⇄C ] ⊚⸢⇄ᵐ⸣ ⇄ᶜ→⇄ᵐ[ A⇄B ] ] ⟆
       ‣ [[ γᵐ[ ⇄ᶜ→⇄ᵐ[ B⇄C ] ⊚⸢⇄ᵐ⸣ ⇄ᶜ→⇄ᵐ[ A⇄B ] ] ⟐ αᵐ[ ⇄ᶜ→⇄ᵐ[ B⇄C ] ⊚⸢⇄ᵐ⸣ ⇄ᶜ→⇄ᵐ[ A⇄B ] ] ]]
       ‣ [[ (γᶜ[ A⇄B ] ⟐ γᶜ[ B⇄C ]) ⟐ (αᶜ[ B⇄C ] ⟐ αᶜ[ A⇄B ]) ]]
       ‣ [focus-right [⟐] 𝑜𝑓 (γᶜ[ A⇄B ] ⟐ γᶜ[ B⇄C ]) ] ⟅ homomorphic[pure/⟐] ⟆⸢≈⸣
       ‣ [[ (γᶜ[ A⇄B ] ⟐ γᶜ[ B⇄C ]) ⟐ pure ⋅ (ηᶜ[ B⇄C ] ∘♮ ηᶜ[ A⇄B ]) ]]
       ∎
  ; reductiveᶜ[_] = let open ProofMode[⊑] in [proof-mode]
      do [[ pure ⋅ (ηᶜ[ B⇄C ] ∘♮ ηᶜ[ A⇄B ]) ⟐ (γᶜ[ A⇄B ] ⟐ γᶜ[ B⇄C ]) ]]
       ‣ [focus-left [⟐] 𝑜𝑓 (γᶜ[ A⇄B ] ⟐ γᶜ[ B⇄C ]) ] ⟅ ◇ homomorphic[pure/⟐] ⟆⸢≈⸣
       ‣ [[ (αᶜ[ B⇄C ] ⟐ αᶜ[ A⇄B ]) ⟐ (γᶜ[ A⇄B ] ⟐ γᶜ[ B⇄C ]) ]]
       ‣ [[ αᵐ[ ⇄ᶜ→⇄ᵐ[ B⇄C ] ⊚⸢⇄ᵐ⸣ ⇄ᶜ→⇄ᵐ[ A⇄B ] ] ⟐ γᵐ[ ⇄ᶜ→⇄ᵐ[ B⇄C ] ⊚⸢⇄ᵐ⸣ ⇄ᶜ→⇄ᵐ[ A⇄B ] ] ]]
       ‣ ⟅ reductiveᵐ[ ⇄ᶜ→⇄ᵐ[ B⇄C ] ⊚⸢⇄ᵐ⸣ ⇄ᶜ→⇄ᵐ[ A⇄B ] ] ⟆
       ‣ [[ return♮ ]]
       ∎
  }

_∧⸢⇄ᶜ⸣_ : ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} → A₁ ⇄ᶜ A₂ → B₁ ⇄ᶜ B₂ → (A₁ ∧♮ B₁) ⇄ᶜ (A₂ ∧♮ B₂)
_∧⸢⇄ᶜ⸣_ {ℓ} {A₁} {A₂} {B₁} {B₂} ⇄A⇄ ⇄B⇄ = mk[⇄ᶜ♭] record
  { η = η
  ; monotonic[η] = monotonic[η]
  ; γ = γ
  ; monotonic[γ] = monotonic[γ]
  ; sound = sound
  ; complete = complete
  }
  where
    η : A₁ ∧♭ B₁ → A₂ ∧♭ B₂
    η ⟨ x , y ⟩ = ⟨ ηᶜ[ ⇄A⇄ ] ⋅ x , ηᶜ[ ⇄B⇄ ] ⋅ y ⟩
    abstract
      monotonic[η] : proper (_⊑_ ⇉ _⊑_) η
      monotonic[η] ⟨ x₁⊑x₂ , y₁⊑y₂ ⟩ = ⟨ res[x][↗]⸢⊑⸣ {f = ηᶜ[ ⇄A⇄ ]} x₁⊑x₂ , res[x][↗]⸢⊑⸣ {f = ηᶜ[ ⇄B⇄ ]} y₁⊑y₂ ⟩
    γ : A₂ ∧♭ B₂ → A₁ ∧♭ B₁ → Set ℓ
    γ ⟨ x♯ , y♯ ⟩ ⟨ x , y ⟩ = (x ⋿ γᶜ[ ⇄A⇄ ] ⋅ x♯) ∧ (y ⋿ γᶜ[ ⇄B⇄ ] ⋅ y♯)
    abstract
      monotonic[γ] : proper (_⊑_ ⇉ _⊒_ ⇉ [→]) γ
      monotonic[γ] ⟨ x₁♯⊑x₂♯ , y₁♯⊑y₂♯ ⟩ ⟨ x₁≽x₂ , y₁≽y₂ ⟩ ⟨ x₁∈γ[x₁♯] , y₁∈γ[y₁♯] ⟩ =
        ⟨ res[Xx][℘]⸢⊑⸣ (res[x][↗]⸢⊑⸣ {f = γᶜ[ ⇄A⇄ ]} x₁♯⊑x₂♯) x₁≽x₂ x₁∈γ[x₁♯]
        , res[Xx][℘]⸢⊑⸣ (res[x][↗]⸢⊑⸣ {f = γᶜ[ ⇄B⇄ ]} y₁♯⊑y₂♯) y₁≽y₂ y₁∈γ[y₁♯]
        ⟩
    sound : ∀ {xy} → γ (η xy) xy
    sound {⟨ x , y ⟩} = ⟨ soundᶜ[ ⇄A⇄ ] {x} , soundᶜ[ ⇄B⇄ ] {y} ⟩
    complete : ∀ {xy♯ xy} → γ xy♯ xy → η xy ⊑ xy♯
    complete {⟨ x♯ , y♯ ⟩} {⟨ x , y ⟩} ⟨ x₁∈γ[x₁♯] , y₁∈γ[y₁♯] ⟩ = ⟨ completeᶜ[ ⇄A⇄ ] x₁∈γ[x₁♯] , completeᶜ[ ⇄B⇄ ] y₁∈γ[y₁♯] ⟩

_↗⸢⇄ᶜ⸣_ : ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} → A₁ ⇄ᶜ A₂ → B₁ ⇄ᶜ B₂ → (A₁ ↗ ℘ B₁) ⇄ (A₂ ↗ ℘ B₂)
_↗⸢⇄ᶜ⸣_ {A₁ = A₁} {A₂} {B₁} {B₂} ⇄A⇄ ⇄B⇄ = ⇄ᶜ→⇄ᵐ[ ⇄A⇄ ] ↗⸢⇄ᵐ⸣ ⇄ᶜ→⇄ᵐ[ ⇄B⇄ ]

ααᶜ[_,_] :
  ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) {f : ⟪ A₁ ↗ ℘ B₁ ⟫} {f♯ : ⟪ A₂ ↗ ℘ B₂ ⟫}
  → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯ ↔ αᶜ[ ⇄B⇄ ] ⟐ f ⊑♮ f♯ ⟐ αᶜ[ ⇄A⇄ ]
ααᶜ[ ⇄A⇄ , ⇄B⇄ ] {f} {f♯} = ⟨ LHS , RHS ⟩
  where
    LHS : α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯ → αᶜ[ ⇄B⇄ ] ⟐ f ⊑♮ f♯ ⟐ αᶜ[ ⇄A⇄ ]
    LHS α[f]⊑f♯ = let open ProofMode[⊑] in [proof-mode]
      do [[ αᶜ[ ⇄B⇄ ] ⟐ f ]]
       ‣ [focus-right [⟐] 𝑜𝑓 αᶜ[ ⇄B⇄ ] ] begin
           do [[ f ]]
            ‣ ⟅ right-unit-extensive[⟐]ᶜ[ ⇄A⇄ ] ⟆
            ‣ [[ f ⟐ γᶜ[ ⇄A⇄ ] ⟐ αᶜ[ ⇄A⇄ ] ]]
            ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
            ‣ [[ (f ⟐ γᶜ[ ⇄A⇄ ]) ⟐ αᶜ[ ⇄A⇄ ] ]]
           end
       ‣ [[ αᶜ[ ⇄B⇄ ] ⟐ (f ⟐ γᶜ[ ⇄A⇄ ]) ⟐ αᶜ[ ⇄A⇄ ] ]]
       ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
       ‣ [[ (αᶜ[ ⇄B⇄ ] ⟐ f ⟐ γᶜ[ ⇄A⇄ ]) ⟐ αᶜ[ ⇄A⇄ ] ]]
       ‣ [[ α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⟐ αᶜ[ ⇄A⇄ ] ]]
       ‣ [focus-left [⟐] 𝑜𝑓 αᶜ[ ⇄A⇄ ] ] ⟅ α[f]⊑f♯ ⟆
       ‣ [[ f♯ ⟐ αᶜ[ ⇄A⇄ ] ]]
       ∎
    RHS : αᶜ[ ⇄B⇄ ] ⟐ f ⊑♮ f♯ ⟐ αᶜ[ ⇄A⇄ ] → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯
    RHS η⟐f⊑f♯⟐η = let open ProofMode[⊑] in [proof-mode]
      do [[ α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ]]
       ‣ [[ αᶜ[ ⇄B⇄ ] ⟐ f ⟐ γᶜ[ ⇄A⇄ ] ]]
       ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
       ‣ [[ (αᶜ[ ⇄B⇄ ] ⟐ f) ⟐ γᶜ[ ⇄A⇄ ] ]]
       ‣ [focus-left [⟐] 𝑜𝑓 γᶜ[ ⇄A⇄ ] ] ⟅ η⟐f⊑f♯⟐η ⟆
       ‣ [[ (f♯ ⟐ αᶜ[ ⇄A⇄ ]) ⟐ γᶜ[ ⇄A⇄ ] ]]
       ‣ ⟅ associative[⟐] ⟆⸢≈⸣
       ‣ [[ f♯ ⟐ αᶜ[ ⇄A⇄ ] ⟐ γᶜ[ ⇄A⇄ ] ]]
       ‣ ⟅ right-unit-reductive[⟐]ᶜ[ ⇄A⇄ ] ⟆
       ‣ [[ f♯ ]]
       ∎

ηηᶜ[_,_] : 
  ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) {f : ⟪ A₁ ↗ B₁ ⟫} {f♯ : ⟪ A₂ ↗ B₂ ⟫}
  → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ (pure ⋅ f) ⊑♮ pure ⋅ f♯ ↔ ηᶜ[ ⇄B⇄ ] ∘♮ f ⊑♮ f♯ ∘♮ ηᶜ[ ⇄A⇄ ]
ηηᶜ[ ⇄A⇄ , ⇄B⇄ ] {f} {f♯} = ⟨ LHS , RHS ⟩
  where
    LHS : α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ (pure ⋅ f) ⊑♮ pure ⋅ f♯ → ηᶜ[ ⇄B⇄ ] ∘♮ f ⊑♮ f♯ ∘♮ ηᶜ[ ⇄A⇄ ]
    LHS α[f]⊑f♯ = injective[pure]⸢⊑⸣ $ let open ProofMode[⊑] in [proof-mode]
      do [[ pure ⋅ (ηᶜ[ ⇄B⇄ ] ∘♮ f) ]]
       ‣ ⟅ ◇ homomorphic[pure/⟐] ⟆⸢≈⸣
       ‣ [[ pure ⋅ ηᶜ[ ⇄B⇄ ] ⟐ pure ⋅ f ]]
       ‣ ⟅ π₁ ααᶜ[ ⇄A⇄ , ⇄B⇄ ] α[f]⊑f♯ ⟆
       ‣ [[ pure ⋅ f♯ ⟐ pure ⋅ ηᶜ[ ⇄A⇄ ] ]]
       ‣ ⟅ homomorphic[pure/⟐] ⟆⸢≈⸣
       ‣ [[ pure ⋅ (f♯ ∘♮ ηᶜ[ ⇄A⇄ ]) ]]
       ∎
    RHS : ηᶜ[ ⇄B⇄ ] ∘♮ f ⊑♮ f♯ ∘♮ ηᶜ[ ⇄A⇄ ] → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ (pure ⋅ f) ⊑♮ pure ⋅ f♯
    RHS η∘f⊑f♯∘η = π₂ ααᶜ[ ⇄A⇄ , ⇄B⇄ ] $ let open ProofMode[⊑] in [proof-mode]
      do [[ pure ⋅ ηᶜ[ ⇄B⇄ ] ⟐ pure ⋅ f ]]
       ‣ ⟅ homomorphic[pure/⟐] ⟆⸢≈⸣
       ‣ [[ pure ⋅ (ηᶜ[ ⇄B⇄ ] ∘♮ f) ]]
       ‣ [focus-right [⋅] 𝑜𝑓 pure ] ⟅ η∘f⊑f♯∘η ⟆
       ‣ ⟅ ◇ homomorphic[pure/⟐] ⟆⸢≈⸣
       ‣ [[ pure ⋅ f♯ ⟐ pure ⋅ ηᶜ[ ⇄A⇄ ] ]]
       ∎

γγᶜ[_,_] :
  ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) {f : ⟪ A₁ ↗ ℘ B₁ ⟫} {f♯ : ⟪ A₂ ↗ ℘ B₂ ⟫}
  → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯ ↔ f ⟐ γᶜ[ ⇄A⇄ ] ⊑♮ γᶜ[ ⇄B⇄ ] ⟐ f♯
γγᶜ[ ⇄A⇄ , ⇄B⇄ ] {f} {f♯} = ⟨ LHS , RHS ⟩
  where
    LHS : α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯ → f ⟐ γᶜ[ ⇄A⇄ ] ⊑♮ γᶜ[ ⇄B⇄ ] ⟐ f♯
    LHS α[f]⊑f♯ = let open ProofMode[⊑] in [proof-mode]
      do [[ f ⟐ γᶜ[ ⇄A⇄ ] ]]
       ‣ ⟅ left-unit-extensive[⟐]ᶜ[ ⇄B⇄ ] ⟆
       ‣ [[ (γᶜ[ ⇄B⇄ ] ⟐ αᶜ[ ⇄B⇄ ]) ⟐ f ⟐ γᶜ[ ⇄A⇄ ] ]]
       ‣ ⟅ associative[⟐] ⟆⸢≈⸣
       ‣ [[ γᶜ[ ⇄B⇄ ] ⟐ αᶜ[ ⇄B⇄ ] ⟐ f ⟐ γᶜ[ ⇄A⇄ ] ]]
       ‣ [[ γᶜ[ ⇄B⇄ ] ⟐ α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ]]
       ‣ [focus-right [⟐] 𝑜𝑓 γᶜ[ ⇄B⇄ ] ] ⟅ α[f]⊑f♯ ⟆
       ‣ [[ γᶜ[ ⇄B⇄ ] ⟐ f♯ ]]
       ∎
    RHS : f ⟐ γᶜ[ ⇄A⇄ ] ⊑♮ γᶜ[ ⇄B⇄ ] ⟐ f♯ → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯
    RHS f⟐γ⊑γ⟐f♯ = let open ProofMode[⊑] in [proof-mode]
      do [[ α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ]]
       ‣ [[ αᶜ[ ⇄B⇄ ] ⟐ f ⟐ γᶜ[ ⇄A⇄ ] ]]
       ‣ [focus-right [⟐] 𝑜𝑓 αᶜ[ ⇄B⇄ ] ] ⟅ f⟐γ⊑γ⟐f♯ ⟆
       ‣ [[ αᶜ[ ⇄B⇄ ] ⟐ γᶜ[ ⇄B⇄ ] ⟐ f♯ ]]
       ‣ ⟅ ◇ associative[⟐] ⟆⸢≈⸣
       ‣ [[ (αᶜ[ ⇄B⇄ ] ⟐ γᶜ[ ⇄B⇄ ]) ⟐ f♯ ]]
       ‣ ⟅ left-unit-reductive[⟐]ᶜ[ ⇄B⇄ ] ⟆
       ‣ [[ f♯ ]]
       ∎
  
γγᶜ[*][_,_] :
  ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) {f : ⟪ A₁ ↗ ℘ B₁ ⟫} {f♯ : ⟪ A₂ ↗ ℘ B₂ ⟫}
  → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯ ↔ (∀ {x} → f *♮ ⋅ (γᶜ[ ⇄A⇄ ] ⋅ x) ⊑♮ γᶜ[ ⇄B⇄ ] *♮ ⋅ (f♯ ⋅ x))
γγᶜ[*][ ⇄A⇄ , ⇄B⇄ ] {f} {f♯} = ⟨ LHS , RHS ⟩
  where
    LHS : α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯ → ∀ {x} → f *♮ ⋅ (γᶜ[ ⇄A⇄ ] ⋅ x) ⊑♮ γᶜ[ ⇄B⇄ ] *♮ ⋅ (f♯ ⋅ x)
    LHS α[f]⊑f♯ {x} = res[f][↗]⸢⊑⸣ {x = x} (π₁ γγᶜ[ ⇄A⇄ , ⇄B⇄ ] α[f]⊑f♯)
    RHS : (∀ {x} → f *♮ ⋅ (γᶜ[ ⇄A⇄ ] ⋅ x) ⊑♮ γᶜ[ ⇄B⇄ ] *♮ ⋅ (f♯ ⋅ x)) → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯
    RHS f[γ[x]]⊑γ[f♯[x]] = π₂ γγᶜ[ ⇄A⇄ , ⇄B⇄ ] $ ext[↗]⸢⊑⸣ $ λ {x} → f[γ[x]]⊑γ[f♯[x]] {x}

γγᶜ[⋅][_,_] :
  ∀ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) {f : ⟪ A₁ ↗ ℘ B₁ ⟫} {f♯ : ⟪ A₂ ↗ ℘ B₂ ⟫}
  → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯ ↔ (∀ {X} → f *♮ ⋅ (γᶜ[ ⇄A⇄ ] *♮ ⋅ X) ⊑♮ γᶜ[ ⇄B⇄ ] *♮ ⋅ (f♯ *♮ ⋅ X))
γγᶜ[⋅][ ⇄A⇄ , ⇄B⇄ ] {f} {f♯} = ⟨ LHS , RHS ⟩
  where
    LHS : α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯ → ∀ {X} → f *♮ ⋅ (γᶜ[ ⇄A⇄ ] *♮ ⋅ X) ⊑♮ γᶜ[ ⇄B⇄ ] *♮ ⋅ (f♯ *♮ ⋅ X)
    LHS α[f]⊑f♯ {X} = let open ProofMode[⊑] in [proof-mode]
      do [[ f *♮ ⋅ (γᶜ[ ⇄A⇄ ] *♮ ⋅ X) ]]
       ‣ ⟅ ◇ associative[*] ⟆⸢≈⸣
       ‣ [[ (f ⟐ γᶜ[ ⇄A⇄ ]) *♮ ⋅ X ]]
       ‣ [focus-left [⋅] 𝑜𝑓 X ] $ [focus-in [*] ] begin
           do [[ f ⟐ γᶜ[ ⇄A⇄ ] ]]
            ‣ ⟅ π₁ γγᶜ[ ⇄A⇄ , ⇄B⇄ ] α[f]⊑f♯ ⟆
            ‣ [[ γᶜ[ ⇄B⇄ ] ⟐ f♯ ]]
           end
       ‣ [[ (γᶜ[ ⇄B⇄ ] ⟐ f♯) *♮ ⋅ X ]]
       ‣ ⟅ associative[*] ⟆⸢≈⸣
       ‣ [[ γᶜ[ ⇄B⇄ ] *♮ ⋅ (f♯ *♮ ⋅ X) ]]
       ∎
    RHS : (∀ {X} → f *♮ ⋅ (γᶜ[ ⇄A⇄ ] *♮ ⋅ X) ⊑♮ γᶜ[ ⇄B⇄ ] *♮ ⋅ (f♯ *♮ ⋅ X)) → α[ ⇄A⇄ ↗⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ f ⊑♮ f♯
    RHS f[γ[X]]⊑γ[f♯[X]] = π₂ γγᶜ[ ⇄A⇄ , ⇄B⇄ ] $ complete[*]⸢⊑⸣ $ ext[↗]⸢⊑⸣ $ λ {X} → let open ProofMode[⊑] in [proof-mode]
      do [[ (f ⟐ γᶜ[ ⇄A⇄ ]) *♮ ⋅ X ]]
       ‣ ⟅ associative[*] ⟆⸢≈⸣
       ‣ [[ f *♮ ⋅ (γᶜ[ ⇄A⇄ ] *♮ ⋅ X) ]]
       ‣ ⟅ f[γ[X]]⊑γ[f♯[X]] ⟆
       ‣ [[ γᶜ[ ⇄B⇄ ] *♮ ⋅ (f♯ *♮ ⋅ X) ]]
       ‣ ⟅ ◇ associative[*] ⟆⸢≈⸣
       ‣ [[ (γᶜ[ ⇄B⇄ ] ⟐ f♯) *♮ ⋅ X ]]
       ∎
