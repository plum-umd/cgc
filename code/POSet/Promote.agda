module POSet.Promote where

open import Prelude
open import POSet.POSet
open import POSet.Fun
open import POSet.Power
open import POSet.Product
open import POSet.ProofMode
open import POSet.Lib

data promote {𝓁} 𝓁' (A : POSet 𝓁) : Set (𝓁 ⊔ˡ 𝓁') where
  ↑⟨_⟩ : ⟪ A ⟫ → promote 𝓁' A

data _⊴⸢promote⸣_ {𝓁 𝓁'} {A : POSet 𝓁} : relation (𝓁 ⊔ˡ 𝓁') (promote 𝓁' A) where
  ↑⟨_⟩ : ∀ {x y} → x ⊑ y → ↑⟨ x ⟩ ⊴⸢promote⸣ ↑⟨ y ⟩

xRx⸢⊴⸢promote⸣⸣ : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → reflexive (_⊴⸢promote⸣_ {𝓁' = 𝓁'} {A})
xRx⸢⊴⸢promote⸣⸣ {x = ↑⟨ x ⟩} = ↑⟨ xRx ⟩

_⌾⸢⊴⸢promote⸣⸣_ : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → transitive (_⊴⸢promote⸣_ {𝓁' = 𝓁'} {A})
↑⟨ y⊑z ⟩ ⌾⸢⊴⸢promote⸣⸣ ↑⟨ x⊑y ⟩ = ↑⟨ y⊑z ⌾ x⊑y ⟩

instance
  Reflexive[⊴⸢promote⸣] : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → Reflexive (_⊴⸢promote⸣_ {𝓁' = 𝓁'} {A})
  Reflexive[⊴⸢promote⸣] = record { xRx = xRx⸢⊴⸢promote⸣⸣ }
  Transitive[⊴⸢promote⸣] : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → Transitive (_⊴⸢promote⸣_ {𝓁' = 𝓁'} {A})
  Transitive[⊴⸢promote⸣] = record { _⌾_ = _⌾⸢⊴⸢promote⸣⸣_ }
  PreOrder[promote] : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → PreOrder (𝓁 ⊔ˡ 𝓁') (promote 𝓁' A)
  PreOrder[promote] = record { _⊴_ = _⊴⸢promote⸣_ }

↑up : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → ⟪ A ⇒ ⇧ (promote 𝓁' A) ⟫
↑up {𝓁' = 𝓁'} {A} = witness-x (curry⸢λ⸣ id⸢λ↑⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → promote 𝓁' A
    fun = ↑⟨_⟩
    abstract
      ppr : proper (_⊑_ ⇉ _⊴_) fun
      ppr x⊑y = ↑⟨ x⊑y ⟩

↑down : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → ⟪ ⇧ (promote 𝓁' A) ⇒ A ⟫
↑down {𝓁' = 𝓁'} {A} = witness-x (curry⸢λ↑⸣ id⸢λ⸣) $ mk[witness] down monotonic[down]
  where
    down : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → promote 𝓁' A → ⟪ A ⟫
    down ↑⟨ x ⟩ = x
    abstract
      monotonic[down] : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → proper (_⊴_ ⇉ _⊑_) (down {𝓁' = 𝓁'} {A})
      monotonic[down] ↑⟨ x⊑y ⟩ = x⊑y

-- why can't I define this???
-- ↑up⸢𝒫⸣ : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → ⟪ 𝒫 A ⇒ 𝒫 (⇧ (promote 𝓁' A)) ⟫
-- ↑up⸢𝒫⸣ {𝓁} {𝓁'} {A} = witness-x (curry⸢λ⸣ id⸢ω↑⸣) $ mk[witness] fun ppr
--   where
--     fun : ⟪ 𝒫 A ⟫ → promote 𝓁' A → Set 𝓁
--     fun X ↑⟨ x ⟩ = x ⋿ X
--     abstract
--       ppr : proper (_⊑_ ⇉ _⊵_ ⇉ [→]) fun
--       ppr X⊑Y ↑⟨ x⊒y ⟩ = res-X-x[ω]⸢⊑⸣ X⊑Y x⊒y

η[promote] : ∀ {𝓁 𝓁'} {A : POSet 𝓁} {x} → ↑up {𝓁' = 𝓁'} {A} ⋅ (↑down {𝓁' = 𝓁'} {A} ⋅ x) ≡ x
η[promote] {x = ↑⟨ ↑⟨ x ⟩ ⟩} = ↯

η[promote]⸢⊙⸣ : ∀ {𝓁 𝓁'} {A : POSet 𝓁} → ↑up {𝓁' = 𝓁'} {A} ⊙ ↑down {𝓁' = 𝓁'} {A} ≈ id⁺
η[promote]⸢⊙⸣ = ext[⇒]⸢≈⸣ $ xRx[≡] η[promote]
