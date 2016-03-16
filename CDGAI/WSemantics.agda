module CDGAI.WSemantics where

open import Prelude
open import Poset
open import CDGAI.ASyntax
open import CDGAI.ASemantics
open import CDGAI.BSyntax
open import CDGAI.BSemantics
open import CDGAI.WSyntax

data _↦ʷ_ {Γ} : wconfig Γ → sconfig Γ → Set where
  Skip : ∀ {ρ} → ⟨ Skip , ρ ⟩ ↦ʷ ⟨ [] , ρ ⟩
  Assign : ∀ {ρ x e i} → ρ ⊢ e ⇓ᵃ i → ⟨ Assign x e , ρ ⟩ ↦ʷ ⟨ [] , ρ [ x ↦ i ] ⟩
  IfTrue : ∀ {ρ be s₁ s₂} → ρ ⊢ be ⇓ᵇ True → ⟨ If be s₁ s₂ , ρ ⟩ ↦ʷ ⟨ s₁ , ρ ⟩
  IfFalse : ∀ {ρ be s₁ s₂} → ρ ⊢ be ⇓ᵇ False → ⟨ If be s₁ s₂ , ρ ⟩ ↦ʷ ⟨ s₂ , ρ ⟩
  WhileTrue : ∀ {ρ be s} → ρ ⊢ be ⇓ᵇ True → ⟨ While be s , ρ ⟩ ↦ʷ ⟨ s ⧺ While be s ∷ [] , ρ ⟩
  WhileFalse : ∀ {ρ be s} → ρ ⊢ be ⇓ᵇ False → ⟨ While be s , ρ ⟩ ↦ʷ ⟨ [] , ρ ⟩

data _↦ˢ_ {Γ} : sconfig Γ → sconfig Γ → Set where
  Step : ∀ {ρ ρ' w s s'} → ⟨ w , ρ ⟩ ↦ʷ ⟨ s' , ρ' ⟩ → ⟨ w ∷ s , ρ ⟩ ↦ˢ ⟨ s' ⧺ s , ρ' ⟩

data _⇓ˢ_ {Γ} : sconfig Γ → sconfig Γ → Set where
  Refl : ∀ {ς} → ς ⇓ˢ ς
  Step  : ∀ {ς₁ ς₂ ς₃} → ς₁ ↦ˢ ς₂ → ς₂ ⇓ˢ ς₃ → ς₁ ⇓ˢ ς₃

xRx⸢⇓ˢ⸣ : ∀ {Γ} {ς : sconfig Γ} → ς ⇓ˢ ς
xRx⸢⇓ˢ⸣ = Refl

_⊚⸢⇓ˢ⸣_ : ∀ {Γ} {ς₁ ς₂ ς₃ : sconfig Γ} → ς₂ ⇓ˢ ς₃ → ς₁ ⇓ˢ ς₂ → ς₁ ⇓ˢ ς₃
bs₂ ⊚⸢⇓ˢ⸣ Refl = bs₂
bs₂ ⊚⸢⇓ˢ⸣ Step ss₁ bs₁ = Step ss₁ (bs₂ ⊚⸢⇓ˢ⸣ bs₁)

one-step : ∀ {Γ} {ς₁ ς₂ : sconfig Γ} → ς₁ ↦ˢ ς₂ → ς₁ ⇓ˢ ς₂
one-step ss = Step ss Refl

⟦⟧⸢↦ˢ⸣ : ∀ {Γ} → ⟪ ⇧ (wexp* Γ) ×♮ ⇧ (env Γ) ↗ 𝒫 (⇧ (wexp* Γ) ×♮ ⇧ (env Γ)) ⟫
⟦⟧⸢↦ˢ⸣ {Γ} = witness (curry⸢λ♮⸣ id⸢ω♮⸣) $ mk[witness] fun ppr[fun]
  where
    fun : prod (⇧ (wexp* Γ)) (⇧ (env Γ)) → prod (⇧ (wexp* Γ)) (⇧ (env Γ)) → Set
    fun (♮⟨ s ⟩ , ♮⟨ ρ ⟩) (♮⟨ s' ⟩ , ♮⟨ ρ' ⟩) = ⟨ s , ρ ⟩ ↦ˢ ⟨ s' , ρ' ⟩
    ppr[fun] : proper (_⊴_ ⇉ flip _⊴_ ⇉ [→]) fun
    ppr[fun] (♮⟨ ↯ ⟩ , ♮⟨ ↯ ⟩) (♮⟨ ↯ ⟩ , ♮⟨ ↯ ⟩) = id

-- data acc[_] {ℓ} {A : Set ℓ} (_R_ : relation ℓ A) (x : A) : Set ℓ where
--   Acc : (∀ y → y R x → acc[ _R_ ] y) → acc[ _R_ ] x
-- 
-- data widen-rel[_] {ℓ} {A : Set ℓ} (_∇_ : A → A → A) : relation ℓ (A × A) where
--   WidenRel : ∀ {x₁ x₂ y₁ y₂} → (x₂ ≡ y₂ ∇ x₁) × (y₂ ≢ x₂) → widen-rel[ _∇_ ] (x₁ , x₂) (y₁ , y₂)
-- 
-- -- (a₁,a₂) ↦ (f a₂,a₂ ∇ f a₂) (f (a₁ ∇ f a₂),(a₂ ∇ f a₂) ∇ f (a₁ ∇ f a₂))
-- --
-- -- **** Attribution ****
-- -- From:
-- --   David Pichardie.
-- --   Building Certified Static Analysers by Modular Construction of Well-founded Lattices.
-- -- and
-- --   David Pichardie's Thesis.
-- pfp-widen : ∀ {ℓ} {A : Set ℓ} {{A-PO : PreOrder ℓ A}} (_∇_ : A → A → A) (cmp : ∀ (x y : A) → x ⊴ y ⨄ not (x ⊴ y)) (f : A → A) (p : A × A) → acc[ widen-rel[ _∇_ ] ] p → ∃ x ⦂ A 𝑠𝑡 f x ⊴ x
-- pfp-widen {A = A} _∇_ cmp f = loop
--   where
--     loop : (p : A × A) → acc[ widen-rel[ _∇_ ] ] p → ∃ x ⦂ A 𝑠𝑡 f x ⊴ x
--     loop (x , y) (Acc h) with f y | remember f y
--     ... | fy | Was ≡fy≡ with cmp fy y
--     ... | Inl f[y]⊴y rewrite ≡fy≡ = ∃ y ,, f[y]⊴y
--     ... | Inr f[y]⋬y = loop (fy , (y ∇ fy)) (h (fy , (y ∇ fy)) (WidenRel (↯ , {!!})))
