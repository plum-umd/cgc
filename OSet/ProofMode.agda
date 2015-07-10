module OSet.ProofMode where

open import Prelude
open import OSet.OSet
open import OSet.Fun
open import OSet.Classes

↑id : ∀ {𝓁} {A : POSet 𝓁} → ⟪ A ⇒ A ⟫
↑id = witness-x (curry⸢λ⸣ id⸢λ⸣) $ mk[witness] id id

↑flip : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} → ⟪ (A ⇒ B ⇒ C) ⇒ B ⇒ A ⇒ C ⟫
↑flip {A = A} {B} {C} = witness-x (curry⸢λ⸣ $ curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⇒ B ⇒ C ⟫ → ⟪ B ⟫ → ⟪ A ⟫ → ⟪ C ⟫
    fun f y x = f ⋅ x ⋅ y
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_ ⇉ _⊑_) fun
      ppr f₁⊑f₂ x₁⊑x₂ y₁⊑y₂ = res-f-x[λ] (res-f-x[λ] f₁⊑f₂ y₁⊑y₂) x₁⊑x₂

infixr 9 _⊙_
_⊙_ : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} → ⟪ B ⇒ C ⟫ → ⟪ A ⇒ B ⟫ → ⟪ A ⇒ C ⟫
_⊙_ {A = A} {B} {C} g f = witness-x (curry⸢λ⸣ id⸢λ⸣) $ mk[witness] fun ppr
  where
    fun : ⟪ A ⟫ → ⟪ C ⟫
    fun x = g ⋅ (f ⋅ x)
    abstract
      ppr : proper (_⊑_ ⇉ _⊑_) fun
      ppr x⊑y = res-x[λ] {f = g} (res-x[λ] {f = f} x⊑y)

abstract
  ⟬_⟭ : ∀ {𝓁} {A : POSet 𝓁} (x : ⟪ A ⟫) → ⟪ A ⟫
  ⟬ x ⟭ = x
  
module §-ProofMode
  (_R_ : ∀ {𝓁} {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫)
  {{R-Refl : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_R_ {A = A})}}
  {{R-Transitive : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_R_ {A = A})}}
  {{R-Logical : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical[λ] (_R_ {A = A}) (_R_ {A = B}) (_R_ {A = A ⇒ B})}}
  (_⦉R⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂))
  {{E : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ ≡ (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) R y → (k ⋅ x₁) R y)}}
  where

  mk[⇰] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) R y → (k ⋅ x₁) R y) → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
  mk[⇰] = change $ ◇⸢≡⸣ E

  un[⇰] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → ∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) R y → (k ⋅ x₁) R y
  un[⇰] = change E

  [proof-mode]_⬜ : ∀ {𝓁} {A : POSet 𝓁} {x₁ x₂ : ⟪ A ⟫} → 𝓁 ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → x₁ R x₂
  [proof-mode] F ⬜ = un[⇰] F {k = ↑id} xRx

  [[_]] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} (x : ⟪ A ⟫) → 𝓁₂ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ x ⟭
  [[ x ]] = mk[⇰] id

  infixr 0  _‣_
  _‣_ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ x₃ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → 𝓁₂ ⦉R⦊ ⟬ x₂ ⟭ ⇰ ⟬ x₃ ⟭ → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₃ ⟭
  _‣_ G F = mk[⇰] $ λ {B} {y} {k} → un[⇰] G {k = k} ∘ un[⇰] F {k = k}

  [R]_⟅_⟆ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ : ⟪ A ⟫} (x₂ : ⟪ A ⟫) (P : x₁ R x₂) → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
  [R] x₂ ⟅ x₁Rx₂ ⟆ = mk[⇰] $ λ {B} {y} {k} P → P ⌾ res-x[λ] {f = k} x₁Rx₂

  [R-≡]_⟅_⟆ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} → {x₁ : ⟪ A ⟫} (x₂ : ⟪ A ⟫) (P : x₁ ≡ x₂) → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
  [R-≡] x₂ ⟅ x₁≡x₂ ⟆ = [R] x₂ ⟅ xRx[≡] x₁≡x₂ ⟆

  [focus-in_] :
    ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} (op : ⟪ A ⇒ B ⟫) {x : ⟪ A ⟫} {y : ⟪ A ⟫}
    → 𝓁₃ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ y ⟭ → 𝓁₃ ⦉R⦊ ⟬ op ⋅ x ⟭ ⇰ ⟬ op ⋅ y ⟭
  [focus-in op ] x⇰y = mk[⇰] $ λ {D} {z} {k} → un[⇰] x⇰y {k = k ⊙ op}

  [focus-left_𝑜𝑓_] :
    ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} (op : ⟪ A ⇒ B ⇒ C ⟫) (z : ⟪ B ⟫) {x y : ⟪ A ⟫} 
    → 𝓁₄ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ y ⟭ → 𝓁₄ ⦉R⦊ ⟬ op ⋅ x ⋅ z ⟭ ⇰ ⟬ op ⋅ y ⋅ z ⟭
  [focus-left op 𝑜𝑓 z ] x⇰y = mk[⇰] $ λ {_ _ k} → un[⇰] x⇰y {k = k ⊙ ↑flip ⋅ op ⋅ z}

  [focus-right_𝑜𝑓_] :
    ∀ {𝓁₁ 𝓁₂ 𝓁₃ 𝓁₄} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {C : POSet 𝓁₃} (op : ⟪ A ⇒ B ⇒ C ⟫) (z : ⟪ A ⟫) {x y : ⟪ B ⟫}
    → 𝓁₄ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ y ⟭ → 𝓁₄ ⦉R⦊ ⟬ op ⋅ z ⋅ x ⟭ ⇰ ⟬ op ⋅ z ⋅ y ⟭
  [focus-right op 𝑜𝑓 z ] x⇰y = mk[⇰] $ λ {_ _ k} → un[⇰] x⇰y {k = k ⊙ op ⋅ z}


--     [→]_⟅_⟆ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ : ⟪ A ⟫} (x₂ : ⟪ A ⟫) → x₁ R x₂ → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
--     [→] x₂ ⟅ x₁Rx₂ ⟆ = [solve] x₁Rx₂
-- 
-- 
--     [focus-x] : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {x₁ x₂ : ⟪ A ⟫} {f : ⟪ A ⇒ B ⟫} → 𝓁₃ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → 𝓁₃ ⦉R⦊ ⟬ f ⋅ x₁ ⟭ ⇰ ⟬ f ⋅ x₂ ⟭
--     [focus-x] F = mk-⇰ $ λ P → un-⇰ F (P ⌾ xRx[≡] β-⊙) ⌾ xRx[≡] η-⊙
-- 
--     [focus-f] : ∀ {𝓁₁ 𝓁₂ 𝓁₃} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {x : ⟪ A ⟫} {f₁ f₂ : ⟪ A ⇒ B ⟫} → 𝓁₃ ⦉R⦊ ⟬ f₁ ⟭ ⇰ ⟬ f₂ ⟭ → 𝓁₃ ⦉R⦊ ⟬ f₁ ⋅ x ⟭ ⇰ ⟬ f₂ ⋅ x ⟭
--     [focus-f] F = mk-⇰ $ λ P → un-⇰ F (P ⌾ xRx[≡] (≡-cong-⇒-x β-apply-to ⌾ β-⊙)) ⌾ xRx[≡] (η-⊙ ⌾ ≡-cong-⇒-x η-apply-to)
-- 
-- module §-ProofMode-Extensional
--   (_R_ : ∀ {𝓁} {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫)
--   {{R-Refl : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_R_ {A = A})}}
--   {{R-Transitive : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_R_ {A = A})}}
--   {{R-Logical : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical (_R_ {A = A}) (_R_ {A = B}) (_R_ {A = A ⇒ B})}}
--   {{R-Extensional : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Extensional (_R_ {A = A}) (_R_ {A = B}) (_R_ {A = A ⇒ B})}}
--   (_⦉R⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂))
--   {{E : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ ≡ (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) R y → (k ⋅ x₁) R y)}}
--   where
--   open §-ProofMode _R_ _⦉R⦊_⇰_ {{E}}
--   [ext] :
--     ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} {f₁ f₂ : ⟪ A ⇒ B ⟫} → (∀ {x} → 𝓁₂ ⦉R⦊ ⟬ f₁ ⋅ x ⟭ ⇰ ⟬ f₂ ⋅ x ⟭) → 𝓁₂ ⦉R⦊ ⟬ f₁ ⟭ ⇰ ⟬ f₂ ⟭
--   [ext] F = mk-⇰ $ λ P → P ⌾ cong-x (ext (un-⇰ F (xRx[≡] β-id) ⌾ xRx[≡] η-id))
-- 
-- module §-ProofMode-Symmetric
--   (_R_ : ∀ {𝓁} {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫)
--   {{R-Refl : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_R_ {A = A})}}
--   {{R-Transitive : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_R_ {A = A})}}
--   {{R-Symmetric : ∀ {𝓁} {A : POSet 𝓁} → Symmetric (_R_ {A = A})}}
--   {{R-Logical : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical (_R_ {A = A}) (_R_ {A = B}) (_R_ {A = A ⇒ B})}}
--   (_⦉R⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂))
--   {{E : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ ≡ (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) R y → (k ⋅ x₁) R y)}}
--   where
--   open §-ProofMode _R_ _⦉R⦊_⇰_ {{E}}
--   [symmetry] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ : ⟪ A ⟫} {x₂ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₂ ⟭ ⇰ ⟬ x₁ ⟭ → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
--   [symmetry] F = mk-⇰ $ λ P → P ⌾ ◇ (un-⇰ F xRx)
-- 
module §-ProofMode-≈-Reflexive
  (_R_ : ∀ {𝓁} {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫)
  {{R-Refl : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_R_ {A = A})}}
  {{R-Transitive : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_R_ {A = A})}}
  {{R-≈-Refl : ∀ {𝓁} {A : POSet 𝓁} → Reflexive[ _≈_ ] (_R_ {A = A})}}
  {{R-Logical : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical[λ] (_R_ {A = A}) (_R_ {A = B}) (_R_ {A = A ⇒ B})}}
  (_⦉R⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂))
  {{E : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ ≡ (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) R y → (k ⋅ x₁) R y)}}
  where
  open §-ProofMode _R_ _⦉R⦊_⇰_ {{E}}
  [≈]_⟅_⟆ : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} → {x₁ : ⟪ A ⟫} (x₂ : ⟪ A ⟫) (P : x₁ ≈ x₂) → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
  [≈] x₂ ⟅ x₁≡x₂ ⟆ = [R] x₂ ⟅ xRx[] x₁≡x₂ ⟆

-- module §-ProofMode-Symmetric[]
--   (_R_ : ∀ {𝓁} {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫)
--   (_REV_ : ∀ {𝓁} {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫)
--   {{R-Refl : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_R_ {A = A})}}
--   {{R-Transitive : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_R_ {A = A})}}
--   {{R-Symmetric : ∀ {𝓁} {A : POSet 𝓁} → Symmetric[ _REV_ ] (_R_ {A = A})}}
--   {{R-Logical : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical (_R_ {A = A}) (_R_ {A = B}) (_R_ {A = A ⇒ B})}}
--   {{REV-Refl : ∀ {𝓁} {A : POSet 𝓁} → Reflexive (_REV_ {A = A})}}
--   {{REV-Transitive : ∀ {𝓁} {A : POSet 𝓁} → Transitive (_REV_ {A = A})}}
--   {{REV-Logical : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {B : POSet 𝓁₂} → Logical (_REV_ {A = A}) (_REV_ {A = B}) (_REV_ {A = A ⇒ B})}}
--   (_⦉R⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂))
--   (_⦉REV⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂))
--   {{R-E : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ ≡ (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) R y → (k ⋅ x₁) R y)}}
--   {{REV-E : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉REV⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ ≡ (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) REV y → (k ⋅ x₁) REV y)}}
--   where
--   module R-ProofMode = §-ProofMode _R_ _⦉R⦊_⇰_ {{R-E}}
--   module REV-ProofMode = §-ProofMode _REV_ _⦉REV⦊_⇰_ {{REV-E}}
--   open R-ProofMode
--   open REV-ProofMode
--   [symmetry←] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ : ⟪ A ⟫} {x₂ : ⟪ A ⟫} → 𝓁₂ ⦉REV⦊ ⟬ x₂ ⟭ ⇰ ⟬ x₁ ⟭ → 𝓁₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
--   [symmetry←] F = R-ProofMode.mk-⇰ $ λ P → P ⌾ ◇←[] (REV-ProofMode.un-⇰ F xRx)
--   [symmetry→] : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ : ⟪ A ⟫} {x₂ : ⟪ A ⟫} → 𝓁₂ ⦉R⦊ ⟬ x₂ ⟭ ⇰ ⟬ x₁ ⟭ → 𝓁₂ ⦉REV⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
--   [symmetry→] F = REV-ProofMode.mk-⇰ $ λ P → P ⌾ ◇→[] (R-ProofMode.un-⇰ F xRx)

abstract
  _⦉_⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} (_R_ : ∀ {𝓁} {A : POSet 𝓁} → relation 𝓁 ⟪ A ⟫) → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂)
  _⦉_⦊_⇰_ 𝓁₂ {A} _R_ x₁ x₂ = ∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) R y → (k ⋅ x₁) R y 

abstract
  _⦉≡⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂)
  𝓁₂ ⦉≡⦊ x₁ ⇰ x₂ = 𝓁₂ ⦉ _≡_ ⦊ x₁ ⇰ x₂
  ⦉≡⦊-E : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉≡⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ ≡ (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) ≡ y → (k ⋅ x₁) ≡ y)
  ⦉≡⦊-E = ↯
  _⦉≈⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂)
  𝓁₂ ⦉≈⦊ x₁ ⇰ x₂ = 𝓁₂ ⦉ _≈_ ⦊ x₁ ⇰ x₂
  ⦉≈⦊-E : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉≈⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ ≡ (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) ≈ y → (k ⋅ x₁) ≈ y)
  ⦉≈⦊-E = ↯
  _⦉⊑⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂)
  𝓁₂ ⦉⊑⦊ x₁ ⇰ x₂ = 𝓁₂ ⦉ _⊑_ ⦊ x₁ ⇰ x₂
  ⦉⊑⦊-E : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉⊑⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ ≡ (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) ⊑ y → (k ⋅ x₁) ⊑ y)
  ⦉⊑⦊-E = ↯
  _⦉⊒⦊_⇰_ : ∀ {𝓁₁} 𝓁₂ {A : POSet 𝓁₁} → ⟪ A ⟫ → ⟪ A ⟫ → Set (𝓁₁ ⊔ˡ sucˡ 𝓁₂)
  𝓁₂ ⦉⊒⦊ x₁ ⇰ x₂ = 𝓁₂ ⦉ _⊒_ ⦊ x₁ ⇰ x₂
  ⦉⊒⦊-E : ∀ {𝓁₁ 𝓁₂} {A : POSet 𝓁₁} {x₁ x₂ : ⟪ A ⟫} → 𝓁₂ ⦉⊒⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ ≡ (∀ {B : POSet 𝓁₂} {y : ⟪ B ⟫} {k : ⟪ A ⇒ B ⟫} → (k ⋅ x₂) ⊒ y → (k ⋅ x₁) ⊒ y)
  ⦉⊒⦊-E = ↯

open §-ProofMode _≡_ _⦉≡⦊_⇰_ {{⦉≡⦊-E}} using () renaming
  ( [proof-mode]_⬜ to [≡-proof-mode]_⬜
  ; [[_]]           to [≡][[_]]
  ; [R]_⟅_⟆          to [≡]_⟅_⟆
  ; _‣_             to _≡‣_
  ; [focus-in_]      to [≡-focus-in_]
  ; [focus-left_𝑜𝑓_]    to [≡-focus-left_𝑜𝑓_]
  ; [focus-right_𝑜𝑓_]   to [≡-focus-right_𝑜𝑓_]
  ) public
-- open §-ProofMode-Symmetric _≡_ _⦉≡⦊_⇰_ {{⦉≡⦊-E}} using () renaming
--   ([symmetry] to [≡-symmetry]) public
-- 

open §-ProofMode _⊑_ _⦉⊑⦊_⇰_ {{⦉⊑⦊-E}} using () renaming
  ( [proof-mode]_⬜ to [⊑-proof-mode]_⬜
  ; [[_]]           to [⊑][[_]]
  ; [R]_⟅_⟆          to [⊑]_⟅_⟆
  ; [R-≡]_⟅_⟆        to [⊑-≡]_⟅_⟆
  ; _‣_              to _⊑‣_
  ; [focus-in_]      to [⊑-focus-in_]
  ; [focus-left_𝑜𝑓_]    to [⊑-focus-left_𝑜𝑓_]
  ; [focus-right_𝑜𝑓_]   to [⊑-focus-right_𝑜𝑓_]
  ) public
open §-ProofMode-≈-Reflexive _⊑_ _⦉⊑⦊_⇰_ {{⦉⊑⦊-E}} using () renaming
  ([≈]_⟅_⟆ to [⊑-≈]_⟅_⟆) public

-- open §-ProofMode _⊒_ _⦉⊒⦊_⇰_ {{⦉⊒⦊-E}} using () renaming
--   ( [proof-mode]_⬜ to [⊑-proof-mode]_⬜
--   ; [[_]]           to [⊑][[_]]
--   ; [R]_⟅_⟆          to [⊑]_⟅_⟆
--   ; [R-≡]_⟅_⟆        to [⊑-≡]_⟅_⟆
--   ; _‣_              to _⊑‣_
--   ; [focus-in_]      to [⊑-focus-in_]
--   ; [focus-left_]    to [⊑-focus-left_]
--   ; [focus-right_]   to [⊑-focus-right_]
--   )

--   ; [focus-x]       to [⊑-focus-x]
--   ; [focus-f]       to [⊑-focus-f]
--   ; [R]_⟅_⟆          to [⊑]_⟅_⟆
--   ; [R-≡]_⟅_⟆        to [⊑-≡]_⟅_⟆
--   ) public
-- open §-ProofMode-Extensional _⊑ᵒ_ _⦉⊑⦊_⇰_ {{⦉⊑⦊-E}} using () renaming
--   ([ext] to [⊑-ext]) public
-- 

open §-ProofMode _≈_ _⦉≈⦊_⇰_ {{⦉≈⦊-E}} using () renaming
  ( [proof-mode]_⬜ to [≈-proof-mode]_⬜
  ; [[_]]           to [≈][[_]]
  ; [R]_⟅_⟆          to [≈]_⟅_⟆
  ; [R-≡]_⟅_⟆        to [≈-≡]_⟅_⟆
  ; _‣_              to _≈‣_
  ; [focus-in_]      to [≈-focus-in_]
  ; [focus-left_𝑜𝑓_]    to [≈-focus-left_𝑜𝑓_]
  ; [focus-right_𝑜𝑓_]   to [≈-focus-right_𝑜𝑓_]
  -- ; [goal]          to [≈-goal]
  -- ; [focus-x]       to [≈-focus-x]
  -- ; [focus-f]       to [≈-focus-f]
  -- ; [R]_⟅_⟆          to [≈]_⟅_⟆
  -- ; [R-≡]_⟅_⟆        to [≈-≡]_⟅_⟆
  ) public
-- open §-ProofMode-Symmetric _≈ᵒ_ _⦉≈⦊_⇰_ {{⦉≈⦊-E}} using () renaming
--   ([symmetry] to [≈-symmetry]) public
-- open §-ProofMode-Extensional _≈ᵒ_ _⦉≈⦊_⇰_ {{⦉≈⦊-E}} using () renaming
--   ([ext] to [≈-ext]) public
-- 
-- open §-ProofMode _⊒ᵒ_ _⦉⊒⦊_⇰_ {{⦉⊒⦊-E}} using () renaming
--   ( [proof-mode]_⬜ to [⊒-proof-mode]_⬜
--   ; [solve]         to [⊒-solve]
--   ; [→]_⟅_⟆          to [⊒-→]_⟅_⟆
--   ; [goal]          to [⊒-goal]
--   ; _‣_             to _⊒‣_
--   ; [focus-x]       to [⊒-focus-x]
--   ; [focus-f]       to [⊒-focus-f]
--   ; [R]_⟅_⟆          to [⊒]_⟅_⟆
--   ; [R-≡]_⟅_⟆        to [⊒-≡]_⟅_⟆
--   ) public
-- open §-ProofMode-≈-Reflexive _⊒ᵒ_ _⦉⊒⦊_⇰_ {{⦉⊒⦊-E}} using () renaming
--   ([≈]_⟅_⟆ to [⊒-≈]_⟅_⟆) public
-- open §-ProofMode-Extensional _⊒ᵒ_ _⦉⊒⦊_⇰_ {{⦉⊒⦊-E}} using () renaming
--   ([ext] to [⊒-ext]) public
-- 
-- open §-ProofMode-Symmetric[] _⊑ᵒ_ _⊒ᵒ_ _⦉⊑⦊_⇰_ _⦉⊒⦊_⇰_ {{⦉⊑⦊-E}} {{⦉⊒⦊-E}} using () renaming
--   ( [symmetry→] to [⊒-symmetry]
--   ; [symmetry←] to [⊑-symmetry]
--   ) public
