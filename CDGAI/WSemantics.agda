module CDGAI.WSemantics where

open import Prelude
open import Poset
open import CDGAI.BoolAbstraction
open import CDGAI.ASyntax
open import CDGAI.ASemantics
open import CDGAI.BSyntax
open import CDGAI.BSemantics
open import CDGAI.WSyntax

module _ {Γ} where
  data _↦ʷ_ : wconfig Γ → sconfig Γ → Set where
    Skip : ∀ {ρ} → ⟨ Skip , ρ ⟩ ↦ʷ ⟨ [] , ρ ⟩
    Assign : ∀ {ρ x e i} → ρ ⊢ e ⇓ᵃ i → ⟨ Assign x e , ρ ⟩ ↦ʷ ⟨ [] , ρ [ x ↦ i ] ⟩
    IfTrue : ∀ {ρ be s₁ s₂} → ρ ⊢ be ⇓ᵇ True → ⟨ If be s₁ s₂ , ρ ⟩ ↦ʷ ⟨ s₁ , ρ ⟩
    IfFalse : ∀ {ρ be s₁ s₂} → ρ ⊢ be ⇓ᵇ False → ⟨ If be s₁ s₂ , ρ ⟩ ↦ʷ ⟨ s₂ , ρ ⟩
    WhileTrue : ∀ {ρ be s} → ρ ⊢ be ⇓ᵇ True → ⟨ While be s , ρ ⟩ ↦ʷ ⟨ s ⧺ˢ While be s ∷ [] , ρ ⟩
    WhileFalse : ∀ {ρ be s} → ρ ⊢ be ⇓ᵇ False → ⟨ While be s , ρ ⟩ ↦ʷ ⟨ [] , ρ ⟩
  
  data _↦ˢ_ : sconfig Γ → sconfig Γ → Set where
    Step : ∀ {ρ ρ' w s s'} → ⟨ w , ρ ⟩ ↦ʷ ⟨ s' , ρ' ⟩ → ⟨ w ∷ s , ρ ⟩ ↦ˢ ⟨ s' ⧺ˢ s , ρ' ⟩
  
  ⟦_⟧ʷ : wexp Γ → ⟪ ⇧ (env Γ) ↗ ℘ (⇧ (sexp Γ) ∧♮ ⇧ (env Γ)) ⟫
  ⟦ w ⟧ʷ = witness (curry⸢λ♭⸣ id⸢ω♭⸣) $ mk[witness] fun ppr
    where
      fun : env Γ → ⇧ (sexp Γ) ∧♭ ⇧ (env Γ) → Set
      fun ρ ⟨ ♮⟨ s′ ⟩ , ♮⟨ ρ′ ⟩ ⟩ = ⟨ w , ρ ⟩ ↦ʷ ⟨ s′ , ρ′ ⟩
      ppr : proper (_⊑_ ⇉ flip _⊑_ ⇉ [→]) fun
      ppr ↯ ⟨ ♮⟨ ↯ ⟩ , ♮⟨ ↯ ⟩ ⟩ = id

  ⟦_⟧ˢ : sexp Γ → ⟪ ⇧ (env Γ) ↗ ℘ (⇧ (sexp Γ) ∧♮ ⇧ (env Γ)) ⟫
  ⟦ s ⟧ˢ = witness (curry⸢λ♭⸣ id⸢ω♭⸣) $ mk[witness] fun ppr[fun]
    where
      fun : env Γ → ⇧ (sexp Γ) ∧♭ ⇧ (env Γ) → Set
      fun ρ ⟨ ♮⟨ s' ⟩ , ♮⟨ ρ' ⟩ ⟩ = ⟨ s , ρ ⟩ ↦ˢ ⟨ s' , ρ' ⟩
      ppr[fun] : proper (_⊑_ ⇉ flip _⊑_ ⇉ [→]) fun
      ppr[fun] ↯ ⟨ ♮⟨ ↯ ⟩ , ♮⟨ ↯ ⟩ ⟩ = id

  β[Skip] : ⟦ Skip ⟧ʷ ⊑♮ pure ⋅ ([,] ⋅ []ˢ♮)
  β[Skip] = ext[↗]⸢⊑⸣ $ λ {ρ} → ext[℘]⸢⊑⸣ (P {ρ})
    where
      P : ∀ {ρ ς} → ς ⋿ ⟦ Skip ⟧ʷ ⋅ ρ → ς ⋿ return♮ ⋅ ⟨ []ˢ♮ ,♮ ρ ⟩
      P {♮⟨ ρ ⟩} {♮⟨ ⟨ ♮⟨ .[] ⟩ , ♮⟨ .ρ ⟩ ⟩ ⟩} Skip = xRx

  β[Assign] : ∀ {x ae} → ⟦ Assign x ae ⟧ʷ ⊑♮ (map℘♮ ⋅ ([,] ⋅ []ˢ♮)) ∘♮ apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ extend♮[ x ] ,♮ ⟦ ae ⟧ᵃ♮ ⟩ ∘♮ split♮
  β[Assign] {x} {ae} = ext[↗]⸢⊑⸣ $ λ {ρ} → ext[℘]⸢⊑⸣ (P {ρ})
    where
      P : ∀ {ρ ς} → ς ⋿ ⟦ Assign x ae ⟧ʷ ⋅ ρ → ς ⋿ (map℘♮ ⋅ ([,] ⋅ []ˢ♮)) ⋅ (apply♮ ⋅ (apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ extend♮[ x ] ,♮ ⟦ ae ⟧ᵃ♮ ⟩ ⋅ (split♮ ⋅ ρ)))
      P {♮⟨ ρ ⟩} {♮⟨ ⟨ ♮⟨ .[] ⟩ , ♮⟨ .(ρ [ x ↦ i ]) ⟩ ⟩ ⟩} (Assign {i = i} ⇓₀) = ∃℘ ♮⟨ ρ [ x ↦ i ] ⟩ ,, (∃℘ ♮⟨ i ⟩ ,, ⇓₀ ,, xRx) ,, xRx

  β[If] : ∀ {be s₁ s₂} → ⟦ If be s₁ s₂ ⟧ʷ ⊑♮ apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ if∘♮ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩) ,♮ ⟦ be ⟧ᵇ ⟩ ∘♮ split♮
  β[If] {be} {s₁} {s₂} = ext[↗]⸢⊑⸣ $ λ {ρ} → ext[℘]⸢⊑⸣ (P {ρ})
    where
      P : ∀ {ρ ς} → ς ⋿ ⟦ If be s₁ s₂ ⟧ʷ ⋅ ρ → ς ⋿ apply♮ ⋅ (apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ if∘♮ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩) ,♮ ⟦ be ⟧ᵇ ⟩ ⋅ (split♮ ⋅ ρ))
      P {♮⟨ ρ ⟩} {♮⟨ ⟨ ♮⟨ .s₁ ⟩ , ♮⟨ .ρ ⟩ ⟩ ⟩} (IfTrue  ⇓₀) = ∃℘ ♮⟨ True  ⟩ ,, ⇓₀ ,, xRx
      P {♮⟨ ρ ⟩} {♮⟨ ⟨ ♮⟨ .s₂ ⟩ , ♮⟨ .ρ ⟩ ⟩ ⟩} (IfFalse ⇓₀) = ∃℘ ♮⟨ False ⟩ ,, ⇓₀ ,, xRx

  β[While] : ∀ {be s} → ⟦ While be s ⟧ʷ ⊑♮ apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ if∘♮ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮) ,♮ ⟦ be ⟧ᵇ ⟩ ∘♮ split♮
  β[While] {be} {s} = ext[↗]⸢⊑⸣ $ λ {ρ} → ext[℘]⸢⊑⸣ (P {ρ})
    where
      P : ∀ {ρ ς} → ς ⋿ ⟦ While be s ⟧ʷ ⋅ ρ → ς ⋿ apply♮ ⋅ (apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ if∘♮ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮) ,♮ ⟦ be ⟧ᵇ ⟩ ⋅ (split♮ ⋅ ρ))
      P {♮⟨ ρ ⟩} {♮⟨ ⟨ ♮⟨ .(s ⧺ˢ (While be s ∷ [])) ⟩ , ♮⟨ .ρ ⟩ ⟩ ⟩} (WhileTrue  ⇓₀) = ∃℘ ♮⟨ True  ⟩ ,, ⇓₀ ,, xRx
      P {♮⟨ ρ ⟩} {♮⟨ ⟨ ♮⟨ .[]                       ⟩ , ♮⟨ .ρ ⟩ ⟩ ⟩} (WhileFalse ⇓₀) = ∃℘ ♮⟨ False ⟩ ,, ⇓₀ ,, xRx
