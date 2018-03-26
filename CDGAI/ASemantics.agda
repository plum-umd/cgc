module CDGAI.ASemantics where

open import Prelude
open import Poset
open import CDGAI.ASyntax

⟦_⟧ᵃ¹ : unary → ℤ → ℤ
⟦ [+] ⟧ᵃ¹ = sucᶻ
⟦ [-] ⟧ᵃ¹ = predᶻ

data _∈⟦_⟧ᵃ²[_,_] : ℤ → binary → ℤ → ℤ → Set where
  [+] : ∀ {n₁ n₂} → (n₁ + n₂) ∈⟦ [+] ⟧ᵃ²[ n₁ , n₂ ]
  [-] : ∀ {n₁ n₂} → (n₁ - n₂) ∈⟦ [-] ⟧ᵃ²[ n₁ , n₂ ]
  [×] : ∀ {n₁ n₂} → (n₁ × n₂) ∈⟦ [×] ⟧ᵃ²[ n₁ , n₂ ]
  [/] : ∀ {n₁ n₂} (n₂≠0 : n₂ ≢ Zero) → (n₁ / n₂ ‖ n₂≠0) ∈⟦ [/] ⟧ᵃ²[ n₁ , n₂ ]
  [%] : ∀ {n₁ n₂} (n₂≠0 : n₂ ≢ Zero) → (n₁ % n₂ ‖ n₂≠0) ∈⟦ [%] ⟧ᵃ²[ n₁ , n₂ ]

data env : context → Set where
  [] : env zero
  _∷_ : ∀ {Γ} → ℤ → env Γ → env (Succ Γ)

instance
  env-PreOrder : ∀ {Γ} → Precision 0ᴸ (env Γ)
  env-PreOrder = mk[Precision] _≡_

_[_] : ∀ {Γ} → env Γ → var Γ → ℤ
(n ∷ ρ) [ Zero ] = n
(n ∷ ρ) [ Succ x ] = ρ [ x ]

_[_↦_] : ∀ {Γ} → env Γ → var Γ → ℤ → env Γ
(i ∷ ρ) [ Zero ↦ i' ] = i' ∷ ρ
(i ∷ ρ) [ Succ x ↦ i' ] = i ∷ (ρ [ x ↦ i' ])

data _⊢_⇓ᵃ_ {Γ} : env Γ → aexp Γ → ℤ → Set where
  Num : ∀ {ρ n} → ρ ⊢ Num n ⇓ᵃ n
  Var : ∀ {ρ x} → ρ ⊢ Var x ⇓ᵃ (ρ [ x ])
  ⊤ℤ : ∀ {ρ n} → ρ ⊢ ⊤ℤ ⇓ᵃ n
  Unary : ∀ {ρ o e n} → ρ ⊢ e ⇓ᵃ n → ρ ⊢ Unary[ o ] e ⇓ᵃ ⟦ o ⟧ᵃ¹ n
  Binary : ∀ {ρ o e₁ e₂ n₁ n₂ n₃} → ρ ⊢ e₁ ⇓ᵃ n₁ → ρ ⊢ e₂ ⇓ᵃ n₂ → n₃ ∈⟦ o ⟧ᵃ²[ n₁ , n₂ ] → ρ ⊢ Binary[ o ] e₁ e₂ ⇓ᵃ n₃

-- Ordered Universe --

⟦_⟧ᵃ¹♮ : unary → ⟪ ⇧ ℤ ↗ ⇧ ℤ ⟫
⟦ o ⟧ᵃ¹♮ = witness (curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] ⟦ o ⟧ᵃ¹ res[•x]

⟦_⟧ᵃ²♮ : binary → ⟪ ⇧ ℤ ↗ ⇧ ℤ ↗ ℘ (⇧ ℤ) ⟫ 
⟦ o ⟧ᵃ²♮ = witness (curry⸢λ♭⸣ $ curry⸢λ♭⸣ id⸢ω♭⸣) $ mk[witness] (λ x y z → z ∈⟦ o ⟧ᵃ²[ x , y ]) ppr
  where
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊒_ ⇉ [→]) (λ x y z → z ∈⟦ o ⟧ᵃ²[ x , y ])
      ppr ↯ ↯ ↯ = id

module _ {Γ} where
  lookup♮[_] : var Γ → ⟪ ⇧ (env Γ) ↗ ⇧ ℤ ⟫
  lookup♮[ x ] = witness (curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] (λ ρ → ρ [ x ]) res[•x]
  
  extend♮[_] : var Γ → ⟪ ⇧ (env Γ) ↗ ⇧ ℤ ↗ ⇧ (env Γ) ⟫
  extend♮[ x ] = witness (curry⸢λ♭⸣ $ curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] (λ ρ i → ρ [ x ↦ i ]) (λ { {x} ↯ ↯ → ↯ })

⟦_⟧ᵃ♮ : ∀ {Γ} → aexp Γ → ⟪ ⇧ (env Γ) ↗ ℘ (⇧ ℤ) ⟫
⟦ e ⟧ᵃ♮ = witness (curry⸢λ♭⸣ id⸢ω♭⸣) $ mk[witness] (λ ρ n → ρ ⊢ e ⇓ᵃ n) ppr
    where
      ppr : proper (_⊑_ ⇉ flip _⊑_ ⇉ [→]) (λ ρ n → ρ ⊢ e ⇓ᵃ n)
      ppr ↯ ↯ = id

𝒞⟦Num⟧⸢⊑⸣ : ∀ {Γ} {n : ℤ} {R : ⟪ ℘ (⇧ (env Γ)) ⟫} → ⟦ Num n ⟧ᵃ♮ *♮ ⋅ R ⊑♮ return♮ ⋅ ♮ n
𝒞⟦Num⟧⸢⊑⸣ {Γ} {n} {R} = ext[℘]⸢⊑⸣ H
  where
    H : ∀ {n'} → n' ⋿ ⟦ Num n ⟧ᵃ♮ *♮ ⋅ R → n' ⊑♮ ♮ n
    H {♮⟨ .n ⟩} (∃℘ x ,, x∈R ,, Num) = xRx

𝒞⟦Num⟧⸢⊒⸣ :
  ∀ {Γ} {n : ℤ} {R : ⟪ ℘ (⇧ (env Γ)) ⟫}
  → ∃ ρ 𝑠𝑡 ρ ⋿ R
  → return♮ ⋅ ♮ n ⊑♮ ⟦ Num n ⟧ᵃ♮ *♮ ⋅ R
𝒞⟦Num⟧⸢⊒⸣ {Γ} {n} {R} ⟨∃ ρ , ρ⋿R ⟩ = π₂ ⟦return⊑X⟧ $ ∃℘ ρ ,, ρ⋿R ,, Num

𝒞⟦Var⟧ : ∀ {Γ} {x : var Γ} {ρ : ⟪ ⇧ (env Γ) ⟫} → ⟦ Var x ⟧ᵃ♮ ⋅ ρ ≈♮ return♮ ⋅ (lookup♮[ x ] ⋅ ρ)
𝒞⟦Var⟧ {Γ} {x} {♮⟨ ρ ⟩} = ext[℘]⸢≈⸣ ⟨ LHS , RHS ⟩
  where
    LHS : ∀ {n} → n ⋿ ⟦ Var x ⟧ᵃ♮ ⋅ ♮ ρ → n ⋿ return♮ ⋅ (lookup♮[ x ] ⋅ ♮ ρ)
    LHS {♮⟨ .(ρ [ x ]) ⟩} Var = xRx
    RHS : ∀ {n} → n ⋿ return♮ ⋅ (lookup♮[ x ] ⋅ ♮ ρ) → n ⋿ ⟦ Var x ⟧ᵃ♮ ⋅ ♮ ρ
    RHS ♮⟨ ↯ ⟩ = Var

𝒞⟦Var⟧⸢∘♮⸣ : ∀ {Γ} {x : var Γ} → ⟦ Var x ⟧ᵃ♮ ≈♮ pure ⋅ lookup♮[ x ]
𝒞⟦Var⟧⸢∘♮⸣ = ext[↗]⸢≈⸣ $ λ {ρ} → 𝒞⟦Var⟧ {ρ = ρ}

𝒞⟦⊤ℤ⟧⸢⊑⸣ : ∀ {Γ} {R : ⟪ ℘ (⇧ (env Γ)) ⟫} → ⟦ ⊤ℤ ⟧ᵃ♮ *♮ ⋅ R ⊑♮ all♮ (⇧ ℤ)
𝒞⟦⊤ℤ⟧⸢⊑⸣ {Γ} {R} = ext[℘]⸢⊑⸣ $ λ {n} → const $ all♮-in {x = n}

𝒞⟦Unary⟧ : ∀ {Γ} {o : unary} {e : aexp Γ} {ρ : ⟪ ⇧ (env Γ) ⟫} → ⟦ Unary[ o ] e ⟧ᵃ♮ ⋅ ρ ≈♮ (pure ⋅ ⟦ o ⟧ᵃ¹♮) *♮ ⋅ (⟦ e ⟧ᵃ♮ ⋅ ρ)
𝒞⟦Unary⟧ {Γ} {o} {e} {ρ} = ext[℘]⸢≈⸣ ⟨ LHS , RHS ⟩
  where
    LHS : ∀ {n} → n ⋿ ⟦ Unary[ o ] e ⟧ᵃ♮ ⋅ ρ → n ⋿ (pure ⋅ ⟦ o ⟧ᵃ¹♮) *♮ ⋅ (⟦ e ⟧ᵃ♮ ⋅ ρ)
    LHS {♮⟨ .(⟦ o ⟧ᵃ¹ n) ⟩} (Unary {n = n} ρ⊢e⇓n) = ∃℘ ♮ n ,, ρ⊢e⇓n ,, xRx
    RHS : ∀ {n} → n ⋿ (pure ⋅ ⟦ o ⟧ᵃ¹♮) *♮ ⋅ (⟦ e ⟧ᵃ♮ ⋅ ρ) → n ⋿ ⟦ Unary[ o ] e ⟧ᵃ♮ ⋅ ρ
    RHS (∃℘ n' ,, ρ⊢e⇓n' ,, ♮⟨ ↯ ⟩) = Unary ρ⊢e⇓n'

𝒞⟦Unary⟧⸢⟐⸣ : ∀ {Γ} {o : unary} {e : aexp Γ} → ⟦ Unary[ o ] e ⟧ᵃ♮ ≈♮ pure ⋅ ⟦ o ⟧ᵃ¹♮ ⟐ ⟦ e ⟧ᵃ♮
𝒞⟦Unary⟧⸢⟐⸣ = ext[↗]⸢≈⸣ $ λ {ρ} → 𝒞⟦Unary⟧ {ρ = ρ}

𝒞⟦Binary⟧⸢*⸣⸢⋿⸣ :
  ∀ {Γ} {o : binary} {e₁ e₂ : aexp Γ} {R : ⟪ ℘ (⇧ (env Γ)) ⟫} {n : ⟪ ⇧ ℤ ⟫}
  → n ⋿ ⟦ Binary[ o ] e₁ e₂ ⟧ᵃ♮ *♮ ⋅ R
  → n ⋿ (uncurry♮ ⋅ ⟦ o ⟧ᵃ²♮) *♮ ⋅ (γ⸢IA⸣ ⋅ ⟨ ⟦ e₁ ⟧ᵃ♮ *♮ ⋅ R ,♮ ⟦ e₂ ⟧ᵃ♮ *♮ ⋅ R ⟩)
𝒞⟦Binary⟧⸢*⸣⸢⋿⸣ {n = n} (∃℘ ρ ,, ρ∈R ,, Binary {n₁ = n₁} {n₂} {.(♭ n)} ρ⊢e₁⇓n₁ ρ⊢e⇓n₂ n₃∈⟦o⟧ᵇ[n₁,n₂]) =
  ∃℘ ♮⟨ ⟨ ♮ n₁ , ♮ n₂ ⟩ ⟩ ,, ⟨ ∃℘ ρ ,, ρ∈R ,, ρ⊢e₁⇓n₁ , ∃℘ ρ ,, ρ∈R ,, ρ⊢e⇓n₂ ⟩ ,, n₃∈⟦o⟧ᵇ[n₁,n₂]

𝒞⟦Binary⟧⸢*⸣⸢⊑⸣ :
  ∀ {Γ} {o : binary} {e₁ e₂ : aexp Γ} {R : ⟪ ℘ (⇧ (env Γ)) ⟫}
  → ⟦ Binary[ o ] e₁ e₂ ⟧ᵃ♮ *♮ ⋅ R ⊑♮ (uncurry♮ ⋅ ⟦ o ⟧ᵃ²♮) *♮ ⋅ (γ⸢IA⸣ ⋅ ⟨ ⟦ e₁ ⟧ᵃ♮ *♮ ⋅ R ,♮ ⟦ e₂ ⟧ᵃ♮ *♮ ⋅ R ⟩)
𝒞⟦Binary⟧⸢*⸣⸢⊑⸣ = ext[℘]⸢⊑⸣ $ λ {n} → 𝒞⟦Binary⟧⸢*⸣⸢⋿⸣ {n = n}
