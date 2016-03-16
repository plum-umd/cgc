module Poset.Promote where

open import Prelude
open import Poset.Poset
open import Poset.Fun
open import Poset.Power
open import Poset.Product
open import Poset.ProofMode
open import Poset.Lib

data promote {ℓ} ℓ' (A : Poset ℓ) : Set (ℓ ⊔ᴸ ℓ') where
  ♮⟨_⟩ : ⟪ A ⟫ → promote ℓ' A

data _⊴⸢promote⸣_ {ℓ ℓ'} {A : Poset ℓ} : relation (ℓ ⊔ᴸ ℓ') (promote ℓ' A) where
  ♮⟨_⟩ : ∀ {x y} → x ⊑ y → ♮⟨ x ⟩ ⊴⸢promote⸣ ♮⟨ y ⟩

xRx⸢⊴⸢promote⸣⸣ : ∀ {ℓ ℓ'} {A : Poset ℓ} → reflexive (_⊴⸢promote⸣_ {ℓ' = ℓ'} {A})
xRx⸢⊴⸢promote⸣⸣ {x = ♮⟨ x ⟩} = ♮⟨ xRx ⟩

_⊚⸢⊴⸢promote⸣⸣_ : ∀ {ℓ ℓ'} {A : Poset ℓ} → transitive (_⊴⸢promote⸣_ {ℓ' = ℓ'} {A})
♮⟨ y⊑z ⟩ ⊚⸢⊴⸢promote⸣⸣ ♮⟨ x⊑y ⟩ = ♮⟨ y⊑z ⊚ x⊑y ⟩

instance
  Reflexive[⊴⸢promote⸣] : ∀ {ℓ ℓ'} {A : Poset ℓ} → Reflexive (_⊴⸢promote⸣_ {ℓ' = ℓ'} {A})
  Reflexive[⊴⸢promote⸣] = record { xRx = xRx⸢⊴⸢promote⸣⸣ }
  Transitive[⊴⸢promote⸣] : ∀ {ℓ ℓ'} {A : Poset ℓ} → Transitive (_⊴⸢promote⸣_ {ℓ' = ℓ'} {A})
  Transitive[⊴⸢promote⸣] = record { _⊚_ = _⊚⸢⊴⸢promote⸣⸣_ }
  PreOrder[promote] : ∀ {ℓ ℓ'} {A : Poset ℓ} → PreOrder (ℓ ⊔ᴸ ℓ') (promote ℓ' A)
  PreOrder[promote] = record { _⊴_ = _⊴⸢promote⸣_ }

♮up : ∀ {ℓ ℓ'} {A : Poset ℓ} → ⟪ A ↗ ⇧ (promote ℓ' A) ⟫
♮up {ℓ' = ℓ'} {A} = witness (curry⸢λ⸣ id⸢λ♮⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → promote ℓ' A
    fun = ♮⟨_⟩
    abstract
      ppr : proper (_⊑_ ⇉ _⊴_) fun
      ppr x⊑y = ♮⟨ x⊑y ⟩

♮down : ∀ {ℓ ℓ'} {A : Poset ℓ} → ⟪ ⇧ (promote ℓ' A) ↗ A ⟫
♮down {ℓ' = ℓ'} {A} = witness (curry⸢λ♮⸣ id⸢λ⸣) $ mk[witness] down monotonic[down]
  where
    down : ∀ {ℓ ℓ'} {A : Poset ℓ} → promote ℓ' A → ⟪ A ⟫
    down ♮⟨ x ⟩ = x
    abstract
      monotonic[down] : ∀ {ℓ ℓ'} {A : Poset ℓ} → proper (_⊴_ ⇉ _⊑_) (down {ℓ' = ℓ'} {A})
      monotonic[down] ♮⟨ x⊑y ⟩ = x⊑y

-- why can't I define this???
-- ♮up⸢𝒫⸣ : ∀ {ℓ ℓ'} {A : Poset ℓ} → ⟪ 𝒫 A ↗ 𝒫 (⇧ (promote ℓ' A)) ⟫
-- ♮up⸢𝒫⸣ {ℓ} {ℓ'} {A} = witness (curry⸢λ⸣ id⸢ω♮⸣) $ mk[witness] fun ppr
--   where
--     fun : ⟪ 𝒫 A ⟫ → promote ℓ' A → Set ℓ
--     fun X ♮⟨ x ⟩ = x ⋿ X
--     abstract
--       ppr : proper (_⊑_ ⇉ _⊵_ ⇉ [→]) fun
--       ppr X⊑Y ♮⟨ x⊒y ⟩ = res-X-x[ω]⸢⊑⸣ X⊑Y x⊒y

η[promote] : ∀ {ℓ ℓ'} {A : Poset ℓ} {x} → ♮up {ℓ' = ℓ'} {A} ⋅ (♮down {ℓ' = ℓ'} {A} ⋅ x) ≡ x
η[promote] {x = ♮⟨ ♮⟨ x ⟩ ⟩} = ↯

η[promote]⸢⊙⸣ : ∀ {ℓ ℓ'} {A : Poset ℓ} → ♮up {ℓ' = ℓ'} {A} ⊙ ♮down {ℓ' = ℓ'} {A} ≈ id♮
η[promote]⸢⊙⸣ = ext⸢≈↗⸣ $ xRx[≡] η[promote]
