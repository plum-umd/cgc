module POSet.FSet where

open import Prelude
open import POSet.POSet
open import POSet.Power
open import POSet.Fun

data fset {𝓁} (A : POSet 𝓁) : Set 𝓁 where
  ↑⟨_⟩ : list-set ⟪ A ⟫ → fset A

data _∈⸢fset⸣_ {𝓁} {A : POSet 𝓁} (x : ⟪ A ⟫) : fset A → Set 𝓁 where
  In : ∀ {y xs} → x ⊑ y → y ∈⸢list-set⸣ xs → x ∈⸢fset⸣ ↑⟨ xs ⟩

data _⊴⸢fset⸣_ {𝓁} {A : POSet 𝓁} : relation 𝓁 (fset A) where
  ↑⟨_⟩ : ∀ {xs ys} → (∀ {x} → x ∈⸢list-set⸣ xs → ∃ y 𝑠𝑡 x ⊑ y × y ∈⸢list-set⸣ ys) → ↑⟨ xs ⟩ ⊴⸢fset⸣ ↑⟨ ys ⟩

xRx⸢⊴⸢fset⸣⸣ : ∀ {𝓁} {A : POSet 𝓁} → reflexive (_⊴⸢fset⸣_ {A = A})
xRx⸢⊴⸢fset⸣⸣ {x = ↑⟨ xs ⟩} = ↑⟨ (λ {x} x∈xs → ∃ x ,, xRx , x∈xs) ⟩

_⌾⸢⊴⸢fset⸣⸣_ : ∀ {𝓁} {A : POSet 𝓁} → transitive (_⊴⸢fset⸣_ {A = A})
_⌾⸢⊴⸢fset⸣⸣_ {x = ↑⟨ xs ⟩} {↑⟨ ys ⟩} {↑⟨ zs ⟩} ↑⟨ ys⊑zs ⟩ ↑⟨ xs⊑ys ⟩ = ↑⟨ P ⟩
  where
    P : ∀ {x} → x ∈⸢list-set⸣ xs → ∃ z 𝑠𝑡 x ⊑ z × z ∈⸢list-set⸣ zs
    P x∈xs with xs⊑ys x∈xs
    ... | ∃ y ,, x⊴y , y∈ys with ys⊑zs y∈ys
    ... | ∃ z ,, y⊴z , z∈zs = ∃ z ,, y⊴z ⌾ x⊴y , z∈zs

instance
  Reflexive[⊴⸢fset⸣⸣] : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_⊴⸢fset⸣_ {A = A})
  Reflexive[⊴⸢fset⸣⸣] = record { xRx = xRx⸢⊴⸢fset⸣⸣ }
  Transitive[⊴⸢fset⸣⸣] : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_⊴⸢fset⸣_ {A = A})
  Transitive[⊴⸢fset⸣⸣] = record { _⌾_ = _⌾⸢⊴⸢fset⸣⸣_ }
  PreOrder[fset] : ∀ {𝓁} {A : POSet 𝓁} → PreOrder 𝓁 (fset A)
  PreOrder[fset] = record { _⊴_ = _⊴⸢fset⸣_ }

