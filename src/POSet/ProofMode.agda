module POSet.ProofMode where

open import Prelude
open import POSet.POSet
open import POSet.Fun
open import POSet.Classes
open import POSet.Lib

abstract
  ⟬_⟭ : ∀ {𝓁} {A : POSet 𝓁} (x : ⟪ A ⟫) → ⟪ A ⟫
  ⟬ x ⟭ = x

  unfold[⟬_⟭] : ∀ {𝓁} {A : POSet 𝓁} (x : ⟪ A ⟫) → ⟬ x ⟭ ≡ x
  unfold[⟬ x ⟭] = ↯

inj[⟬⟭] : ∀ {𝓁} {A : POSet 𝓁} {x y : ⟪ A ⟫} → ⟬ x ⟭ ≡ ⟬ y ⟭ → x ≡ y
inj[⟬⟭] {x = x} {y} rewrite unfold[⟬ x ⟭] | unfold[⟬ y ⟭] = id
  
_⦉_⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} (_R_ : ∀ {𝓁} {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫) → relation (𝓁₁ ⊔ˡ sucˡ 𝓁₂) ⟪ A ⟫
_⦉_⦊_⇰_ 𝓁₂ {A} _R_ x₁ x₂ = ∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) R y → (k ⋅ x₁) R y 

module §-ProofMode
  (_R_ : ∀ {𝓁} {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫)
  {{R-Refl : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_R_ {A = A})}}
  {{R-Transitive : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_R_ {A = A})}}
  {{R-Logical : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical[⇒] (_R_ {A = A}) (_R_ {A = B}) (_R_ {A = A ⇒ B})}}
  (_⦉R⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → relation (𝓁₁ ⊔ˡ sucˡ 𝓁₂) ⟪ A ⟫)
  (mk[⇰] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉ _R_ ⦊ x₁ ⇰ x₂ → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭)
  (un[⇰] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → 𝓁₂ ⦉ _R_ ⦊ x₁ ⇰ x₂)
  where
  [proof-mode]_∎ : ∀ {𝓁} {A : POSet 𝓁} {x₁ x₂ : ⟪ A ⟫} → 𝓁 ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → x₁ R x₂
  [proof-mode] F ∎ = un[⇰] F {k = id⁺} xRx

  infixr 0  _‣_
  _‣_ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ x₃ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → 𝓁₂ ⦉R⦊ ⟬ x₂ ⟭ ⇰ ⟬ x₃ ⟭ → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₃ ⟭
  _‣_ G F = mk[⇰] $ λ {B} {y} {k} → un[⇰] G {k = k} ∘ un[⇰] F {k = k}

  [[_]] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} (x : ⟪ A ⟫) → 𝓁₂ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ x ⟭
  [[ x ]] = mk[⇰] id

  ⟅_⟆ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → x₁ R x₂ → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
  ⟅ x₁Rx₂ ⟆ = mk[⇰] $ λ {B} {y} {k} P → P ⌾ res-x[⇒] {f = k} x₁Rx₂

  ⟅_⟆⸢≡⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} → {x₁ x₂ : ⟪ A ⟫} (P : x₁ ≡ x₂) → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
  ⟅ x₁≡x₂ ⟆⸢≡⸣ = ⟅ xRx[≡] x₁≡x₂ ⟆

  [focus-in_] :
    ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} (op : ⟪ A ⇒ B ⟫) {x : ⟪ A ⟫} {y : ⟪ A ⟫}
    → 𝓁₃ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ y ⟭ → 𝓁₃ ⦉R⦊ ⟬ op ⋅ x ⟭ ⇰ ⟬ op ⋅ y ⟭
  [focus-in op ] x⇰y = mk[⇰] $ λ {D} {z} {k} → un[⇰] x⇰y {k = k ⊙ op}

  [focus-left_𝑜𝑓_] :
    ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} (op : ⟪ A ⇒ B ⇒ C ⟫) (z : ⟪ B ⟫) {x y : ⟪ A ⟫} 
    → 𝓁₄ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ y ⟭ → 𝓁₄ ⦉R⦊ ⟬ op ⋅ x ⋅ z ⟭ ⇰ ⟬ op ⋅ y ⋅ z ⟭
  [focus-left op 𝑜𝑓 z ] x⇰y = mk[⇰] $ λ {_ _ k} → un[⇰] x⇰y {k = k ⊙ flip⁺ ⋅ op ⋅ z}

  [focus-right_𝑜𝑓_] :
    ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} (op : ⟪ A ⇒ B ⇒ C ⟫) (z : ⟪ A ⟫) {x y : ⟪ B ⟫}
    → 𝓁₄ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ y ⟭ → 𝓁₄ ⦉R⦊ ⟬ op ⋅ z ⋅ x ⟭ ⇰ ⟬ op ⋅ z ⋅ y ⟭
  [focus-right op 𝑜𝑓 z ] x⇰y = mk[⇰] $ λ {_ _ k} → un[⇰] x⇰y {k = k ⊙ op ⋅ z}

  module §-Reflexive[≈]
    {{R-Refl[≈] : ∀ {𝓁} {A : POSet 𝓁} → Reflexive[ _≈_ ] (_R_ {A = A})}}
    where
    ⟅_⟆⸢≈⸣ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} → {x₁ x₂ : ⟪ A ⟫} (P : x₁ ≈ x₂) → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
    ⟅ x₁≈x₂ ⟆⸢≈⸣ = ⟅ xRx[] x₁≈x₂ ⟆

data _⦉⊑⦊_⇰_ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} : relation (𝓁₁ ⊔ˡ sucˡ 𝓁₂) ⟪ A ⟫ where
  mk[⦉⊑⦊]-≡ : ∀ {x₁ x₂ x₃ x₄ : ⟪ A ⟫} → x₃ ≡ ⟬ x₁ ⟭ → x₄ ≡ ⟬ x₂ ⟭ → 𝓁₂ ⦉ _⊑_ ⦊ x₁ ⇰ x₂ → 𝓁₂ ⦉⊑⦊ x₃ ⇰ x₄

mk[⦉⊑⦊] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉ _⊑_ ⦊ x₁ ⇰ x₂ → 𝓁₂ ⦉⊑⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
mk[⦉⊑⦊] = mk[⦉⊑⦊]-≡ ↯ ↯

un[⦉⊑⦊] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉⊑⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → 𝓁₂ ⦉ _⊑_ ⦊ x₁ ⇰ x₂
un[⦉⊑⦊] (mk[⦉⊑⦊]-≡ E₁ E₂ P) rewrite inj[⟬⟭] E₁ | inj[⟬⟭] E₂ = λ {B} {y} {k} → P {B} {y} {k}

module §-ProofMode[⊑] where
  open §-ProofMode _⊑_ _⦉⊑⦊_⇰_ mk[⦉⊑⦊] un[⦉⊑⦊] public
  open §-Reflexive[≈] public

open §-ProofMode[⊑] using () renaming
  ( [proof-mode]_∎     to [proof-mode]⸢⊑⸣_∎
  ; _‣_                to _‣⸢⊑⸣_
  ; [[_]]              to [[_]]⸢⊑⸣
  ; ⟅_⟆                to ⟅_⟆⸢⊑⸣
  ; ⟅_⟆⸢≡⸣             to ⟅_⟆⸢⊑-≡⸣
  ; [focus-in_]        to [focus-in_]⸢⊑⸣
  ; [focus-left_𝑜𝑓_]   to [focus-left_𝑜𝑓_]⸢⊑⸣
  ; [focus-right_𝑜𝑓_]  to [focus-right_𝑜𝑓_]⸢⊑⸣
  ; ⟅_⟆⸢≈⸣             to ⟅_⟆⸢⊑-≈⸣
  ) public

data _⦉≈⦊_⇰_ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} : relation (𝓁₁ ⊔ˡ sucˡ 𝓁₂) ⟪ A ⟫ where
  mk[⦉≈⦊]-≡ : ∀ {x₁ x₂ x₃ x₄ : ⟪ A ⟫} → x₃ ≡ ⟬ x₁ ⟭ → x₄ ≡ ⟬ x₂ ⟭ → 𝓁₂ ⦉ _≈_ ⦊ x₁ ⇰ x₂ → 𝓁₂ ⦉≈⦊ x₃ ⇰ x₄

mk[⦉≈⦊] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉ _≈_ ⦊ x₁ ⇰ x₂ → 𝓁₂ ⦉≈⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
mk[⦉≈⦊] = mk[⦉≈⦊]-≡ ↯ ↯

un[⦉≈⦊] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉≈⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → 𝓁₂ ⦉ _≈_ ⦊ x₁ ⇰ x₂
un[⦉≈⦊] (mk[⦉≈⦊]-≡ E₁ E₂ P) rewrite inj[⟬⟭] E₁ | inj[⟬⟭] E₂ = λ {B} {y} {k} → P {B} {y} {k}

module §-ProofMode[≈] where
  open §-ProofMode _≈_ _⦉≈⦊_⇰_ mk[⦉≈⦊] un[⦉≈⦊] public
open §-ProofMode[≈] using () renaming
  ( [proof-mode]_∎    to [proof-mode]⸢≈⸣_∎
  ; _‣_                to _‣⸢≈⸣_
  ; [[_]]            to [[_]]⸢≈⸣
  ; ⟅_⟆              to ⟅_⟆⸢≈-≈⸣
  ; ⟅_⟆⸢≡⸣            to ⟅_⟆⸢≈-≡⸣
  ; [focus-in_]       to [focus-in_]⸢≈⸣
  ; [focus-left_𝑜𝑓_]  to [focus-left_𝑜𝑓_]⸢≈⸣
  ; [focus-right_𝑜𝑓_] to [focus-right_𝑜𝑓_]⸢≈⸣
  ) public

data _⦉≡⦊_⇰_ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} : relation (𝓁₁ ⊔ˡ sucˡ 𝓁₂) ⟪ A ⟫ where
  mk[⦉≡⦊]-≡ : ∀ {x₁ x₂ x₃ x₄ : ⟪ A ⟫} → x₃ ≡ ⟬ x₁ ⟭ → x₄ ≡ ⟬ x₂ ⟭ → 𝓁₂ ⦉ _≡_ ⦊ x₁ ⇰ x₂ → 𝓁₂ ⦉≡⦊ x₃ ⇰ x₄

mk[⦉≡⦊] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉ _≡_ ⦊ x₁ ⇰ x₂ → 𝓁₂ ⦉≡⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
mk[⦉≡⦊] = mk[⦉≡⦊]-≡ ↯ ↯

un[⦉≡⦊] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉≡⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → 𝓁₂ ⦉ _≡_ ⦊ x₁ ⇰ x₂
un[⦉≡⦊] (mk[⦉≡⦊]-≡ E₁ E₂ P) rewrite inj[⟬⟭] E₁ | inj[⟬⟭] E₂ = λ {B} {y} {k} → P {B} {y} {k}

module §-ProofMode[≡] where
  open §-ProofMode _≡_ _⦉≡⦊_⇰_ mk[⦉≡⦊] un[⦉≡⦊] public
open §-ProofMode[≡] using () renaming
  ( [proof-mode]_∎     to [proof-mode]⸢≡⸣_∎
  ; _‣_                to _‣⸢≡⸣_
  ; [[_]]              to [[_]]⸢≡⸣
  ; ⟅_⟆                to ⟅_⟆⸢≡-≡⸣
  ; [focus-in_]        to [focus-in_]⸢≡⸣
  ; [focus-left_𝑜𝑓_]   to [focus-left_𝑜𝑓_]⸢≡⸣
  ; [focus-right_𝑜𝑓_]  to [focus-right_𝑜𝑓_]⸢≡⸣
  ) public

-- record ProofMode {𝓁} (_R_ : ∀ {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫) (⦉R⦊_⇰_ : ∀ {A : POSet 𝓁} → relation (sucˡ 𝓁) ⟪ A ⟫) : Set (sucˡ 𝓁) where
--   field
--     [proof-mode]_∎ : ∀ {A : POSet 𝓁} {x₁ x₂ : ⟪ A ⟫} → ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → x₁ R x₂
-- open ProofMode {{...}} public
-- 
-- record ProofState {𝓁₁ 𝓁₂} (⦉R⦊_⇰_ : ∀ {A : POSet 𝓁₁} → relation (𝓁₁ ⊔ˡ sucˡ 𝓁₂) ⟪ A ⟫) : Set (sucˡ (𝓁₁ ⊔ˡ 𝓁₂)) where
--   infixr 0 _‣_
--   field
--     _‣_ : ∀ {A : POSet 𝓁₁} {x₁ x₂ x₃ : ⟪ A ⟫} → ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → ⦉R⦊ ⟬ x₂ ⟭ ⇰ ⟬ x₃ ⟭ → ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₃ ⟭
--     [[_]] : ∀ {A : POSet 𝓁₁} (x : ⟪ A ⟫) → ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ x ⟭
-- open ProofState {{...}} public
-- 
-- record ProofStep {𝓁₁ 𝓁₂} (_R_ : ∀ {A : POSet 𝓁₁} → relation 𝓁₁ ⟪ A ⟫) (⦉R⦊_⇰_ : ∀ {A : POSet 𝓁₁} → relation (𝓁₁ ⊔ˡ sucˡ 𝓁₂) ⟪ A ⟫) : Set (sucˡ (𝓁₁ ⊔ˡ 𝓁₂)) where
--   field
--     ⟅_⟆ : ∀ {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → x₁ R x₂ → ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
-- open ProofStep {{...}} public
-- 
-- record ProofFocusIn {𝓁₁ 𝓁₂ 𝓁₃}
--   (⦉R⦊₁_⇰_ : ∀ {A : POSet 𝓁₁} → relation (𝓁₁ ⊔ˡ sucˡ 𝓁₃) ⟪ A ⟫)
--   (⦉R⦊₂_⇰_ : ∀ {A : POSet 𝓁₂} → relation (𝓁₂ ⊔ˡ sucˡ 𝓁₃) ⟪ A ⟫)
--   : Set (sucˡ (𝓁₁ ⊔ˡ 𝓁₂ ⊔ˡ 𝓁₃)) where
--   field
--     [focus-in_] : ∀ {A : POSet 𝓁₁} {B : POSet 𝓁₂} (op : ⟪ A ⇒ B ⟫) {x : ⟪ A ⟫} {y : ⟪ A ⟫} → ⦉R⦊₁ ⟬ x ⟭ ⇰ ⟬ y ⟭ → ⦉R⦊₂ ⟬ op ⋅ x ⟭ ⇰ ⟬ op ⋅ y ⟭
-- open ProofFocusIn {{...}} public
-- 
-- record ProofFocusLeft {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄}
--   (⦉R⦊₁_⇰_ : ∀ {A : POSet 𝓁₁} → relation (𝓁₁ ⊔ˡ sucˡ 𝓁₄) ⟪ A ⟫)
--   (⦉R⦊₃_⇰_ : ∀ {A : POSet 𝓁₃} → relation (𝓁₃ ⊔ˡ sucˡ 𝓁₄) ⟪ A ⟫)
--   : Set (sucˡ (𝓁₁ ⊔ˡ 𝓁₂ ⊔ˡ 𝓁₃ ⊔ˡ 𝓁₄)) where
--   field
--     [focus-left_𝑜𝑓_] :
--       ∀ {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} (op : ⟪ A ⇒ B ⇒ C ⟫) (z : ⟪ B ⟫) {x y : ⟪ A ⟫} 
--       → ⦉R⦊₁ ⟬ x ⟭ ⇰ ⟬ y ⟭ → ⦉R⦊₃ ⟬ op ⋅ x ⋅ z ⟭ ⇰ ⟬ op ⋅ y ⋅ z ⟭
-- open ProofFocusLeft {{...}} public
-- 
-- record ProofFocusRight {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄}
--   (⦉R⦊₂_⇰_ : ∀ {A : POSet 𝓁₂} → relation (𝓁₂ ⊔ˡ sucˡ 𝓁₄) ⟪ A ⟫)
--   (⦉R⦊₃_⇰_ : ∀ {A : POSet 𝓁₃} → relation (𝓁₃ ⊔ˡ sucˡ 𝓁₄) ⟪ A ⟫)
--   : Set (sucˡ (𝓁₁ ⊔ˡ 𝓁₂ ⊔ˡ 𝓁₃ ⊔ˡ 𝓁₄)) where
--   field
--     [focus-right_𝑜𝑓_] :
--       ∀ {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} (op : ⟪ A ⇒ B ⇒ C ⟫) (z : ⟪ A ⟫) {x y : ⟪ B ⟫}
--       → ⦉R⦊₂ ⟬ x ⟭ ⇰ ⟬ y ⟭ → ⦉R⦊₃ ⟬ op ⋅ z ⋅ x ⟭ ⇰ ⟬ op ⋅ z ⋅ y ⟭
-- open ProofFocusRight {{...}} public

-- instance
--   ProofMode[⊑] : ∀ {𝓁} → ProofMode {𝓁} _⊑_ (_⦉⊑⦊_⇰_ 𝓁)
--   ProofMode[⊑] = record { [proof-mode]_∎ = §-ProofMode[⊑].[R-proof-mode]_∎ }
--   ProofState[⊑] : ∀ {𝓁₁ 𝓁₂} → ProofState {𝓁₁} {𝓁₂} (_⦉⊑⦊_⇰_ 𝓁₂)
--   ProofState[⊑] = record { _‣_ = §-ProofMode[⊑]._R‣_ ; [[_]] = §-ProofMode[⊑].[R][[_]]}
--   ProofStep[⊑] : ∀ {𝓁₁ 𝓁₂} → ProofStep {𝓁₁} {𝓁₂} _⊑_ (_⦉⊑⦊_⇰_ 𝓁₂)
--   ProofStep[⊑] = record { ⟅_⟆ = §-ProofMode[⊑].[R]⟅_⟆ }
--   ProofStep[⊑-≡] : ∀ {𝓁₁ 𝓁₂} → ProofStep {𝓁₁} {𝓁₂} _≡_ (_⦉⊑⦊_⇰_ 𝓁₂)
--   ProofStep[⊑-≡] = record { ⟅_⟆ = §-ProofMode[⊑].[R-≡]⟅_⟆ }
--   ProofStep[⊑-≈] : ∀ {𝓁₁ 𝓁₂} → ProofStep {𝓁₁} {𝓁₂} _≈_ (_⦉⊑⦊_⇰_ 𝓁₂)
--   ProofStep[⊑-≈] = record { ⟅_⟆ = §-ProofMode[⊑].§-Reflexive[≈].[R-≈]⟅_⟆ }
--   ProofFocusIn[⊑] : ∀ {𝓁₁ 𝓁₂ 𝓁₃} → ProofFocusIn {𝓁₁} {𝓁₂} {𝓁₃} (_⦉⊑⦊_⇰_ 𝓁₃) (_⦉⊑⦊_⇰_ 𝓁₃)
--   ProofFocusIn[⊑] = record { [focus-in_] = §-ProofMode[⊑].[R-focus-in_] }
--   ProofFocusLeft[⊑] : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} → ProofFocusLeft {𝓁₁} {𝓁₂} {𝓁₃} {𝓁₄} (_⦉⊑⦊_⇰_ 𝓁₄) (_⦉⊑⦊_⇰_ 𝓁₄)
--   ProofFocusLeft[⊑] = record { [focus-left_𝑜𝑓_] = §-ProofMode[⊑].[R-focus-left_𝑜𝑓_] }
--   ProofFocusRight[⊑] : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} → ProofFocusRight {𝓁₁} {𝓁₂} {𝓁₃} {𝓁₄} (_⦉⊑⦊_⇰_ 𝓁₄) (_⦉⊑⦊_⇰_ 𝓁₄)
--   ProofFocusRight[⊑] = record { [focus-right_𝑜𝑓_] = §-ProofMode[⊑].[R-focus-right_𝑜𝑓_] }
-- 
-- instance
--   ProofMode[≈] : ∀ {𝓁} → ProofMode {𝓁} _≈_ (_⦉≈⦊_⇰_ 𝓁)
--   ProofMode[≈] = record { [proof-mode]_∎ = §-ProofMode[≈].[R-proof-mode]_∎ }
--   ProofState[≈] : ∀ {𝓁₁ 𝓁₂} → ProofState {𝓁₁} {𝓁₂} (_⦉≈⦊_⇰_ 𝓁₂)
--   ProofState[≈] = record { _‣_ = §-ProofMode[≈]._R‣_ ; [[_]] = §-ProofMode[≈].[R][[_]]}
--   ProofStep[≈] : ∀ {𝓁₁ 𝓁₂} → ProofStep {𝓁₁} {𝓁₂} _≈_ (_⦉≈⦊_⇰_ 𝓁₂)
--   ProofStep[≈] = record { ⟅_⟆ = §-ProofMode[≈].[R]⟅_⟆ }
--   ProofStep[≈-≡] : ∀ {𝓁₁ 𝓁₂} → ProofStep {𝓁₁} {𝓁₂} _≡_ (_⦉≈⦊_⇰_ 𝓁₂)
--   ProofStep[≈-≡] = record { ⟅_⟆ = §-ProofMode[≈].[R-≡]⟅_⟆ }
--   ProofFocusIn[≈] : ∀ {𝓁₁ 𝓁₂ 𝓁₃} → ProofFocusIn {𝓁₁} {𝓁₂} {𝓁₃} (_⦉≈⦊_⇰_ 𝓁₃) (_⦉≈⦊_⇰_ 𝓁₃)
--   ProofFocusIn[≈] = record { [focus-in_] = §-ProofMode[≈].[R-focus-in_] }
--   ProofFocusLeft[≈] : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} → ProofFocusLeft {𝓁₁} {𝓁₂} {𝓁₃} {𝓁₄} (_⦉≈⦊_⇰_ 𝓁₄) (_⦉≈⦊_⇰_ 𝓁₄)
--   ProofFocusLeft[≈] = record { [focus-left_𝑜𝑓_] = §-ProofMode[≈].[R-focus-left_𝑜𝑓_] }
--   ProofFocusRight[≈] : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} → ProofFocusRight {𝓁₁} {𝓁₂} {𝓁₃} {𝓁₄} (_⦉≈⦊_⇰_ 𝓁₄) (_⦉≈⦊_⇰_ 𝓁₄)
--   ProofFocusRight[≈] = record { [focus-right_𝑜𝑓_] = §-ProofMode[≈].[R-focus-right_𝑜𝑓_] }
-- 
-- instance
--   ProofMode[≡] : ∀ {𝓁} → ProofMode {𝓁} _≡_ (_⦉≡⦊_⇰_ 𝓁)
--   ProofMode[≡] = record { [proof-mode]_∎ = §-ProofMode[≡].[R-proof-mode]_∎ }
--   ProofState[≡] : ∀ {𝓁₁ 𝓁₂} → ProofState {𝓁₁} {𝓁₂} (_⦉≡⦊_⇰_ 𝓁₂)
--   ProofState[≡] = record { _‣_ = §-ProofMode[≡]._R‣_ ; [[_]] = §-ProofMode[≡].[R][[_]]}
--   ProofStep[≡] : ∀ {𝓁₁ 𝓁₂} → ProofStep {𝓁₁} {𝓁₂} _≡_ (_⦉≡⦊_⇰_ 𝓁₂)
--   ProofStep[≡] = record { ⟅_⟆ = §-ProofMode[≡].[R]⟅_⟆ }
--   ProofFocusIn[≡] : ∀ {𝓁₁ 𝓁₂ 𝓁₃} → ProofFocusIn {𝓁₁} {𝓁₂} {𝓁₃} (_⦉≡⦊_⇰_ 𝓁₃) (_⦉≡⦊_⇰_ 𝓁₃)
--   ProofFocusIn[≡] = record { [focus-in_] = §-ProofMode[≡].[R-focus-in_] }
--   ProofFocusLeft[≡] : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} → ProofFocusLeft {𝓁₁} {𝓁₂} {𝓁₃} {𝓁₄} (_⦉≡⦊_⇰_ 𝓁₄) (_⦉≡⦊_⇰_ 𝓁₄)
--   ProofFocusLeft[≡] = record { [focus-left_𝑜𝑓_] = §-ProofMode[≡].[R-focus-left_𝑜𝑓_] }
--   ProofFocusRight[≡] : ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} → ProofFocusRight {𝓁₁} {𝓁₂} {𝓁₃} {𝓁₄} (_⦉≡⦊_⇰_ 𝓁₄) (_⦉≡⦊_⇰_ 𝓁₄)
--   ProofFocusRight[≡] = record { [focus-right_𝑜𝑓_] = §-ProofMode[≡].[R-focus-right_𝑜𝑓_] }
