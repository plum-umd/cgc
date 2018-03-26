module Poset.ProofMode where

open import Prelude
open import Poset.Poset
open import Poset.Fun
open import Poset.Classes
open import Poset.Lib

abstract
  ⟬_⟭ : ∀ {ℓ} {A : Poset ℓ} (x : ⟪ A ⟫) → ⟪ A ⟫
  ⟬ x ⟭ = x

  unfold[⟬_⟭] : ∀ {ℓ} {A : Poset ℓ} (x : ⟪ A ⟫) → ⟬ x ⟭ ≡ x
  unfold[⟬ x ⟭] = ↯

inj[⟬⟭] : ∀ {ℓ} {A : Poset ℓ} {x y : ⟪ A ⟫} → ⟬ x ⟭ ≡ ⟬ y ⟭ → x ≡ y
inj[⟬⟭] {x = x} {y} rewrite unfold[⟬ x ⟭] | unfold[⟬ y ⟭] = id
  
_⦉_⦊_⇰_ : ∀ {ℓ₁} ℓ₂ {A : Poset ℓ₁} (_R_ : ∀ {ℓ} {A : Poset ℓ} → relation ℓ ⟪ A ⟫) → relation (ℓ₁ ⊔ᴸ ↑ᴸ ℓ₂) ⟪ A ⟫
_⦉_⦊_⇰_ ℓ₂ {A} _R_ x₁ x₂ = ∀ {B : Poset ℓ₂} {y : ⟪ B ⟫} {k : ⟪ A ↗ B ⟫} → (k ⋅ x₂) R y → (k ⋅ x₁) R y 

module ProofMode
  (_R_ : ∀ {ℓ} {A : Poset ℓ} → relation ℓ ⟪ A ⟫)
  {{R-Refl : ∀ {ℓ} {A : Poset ℓ} → Reflexive (_R_ {A = A})}}
  {{R-Transitive : ∀ {ℓ} {A : Poset ℓ} → Transitive (_R_ {A = A})}}
  (res[fx][↗] :
     ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} {f g : ⟪ A ↗ B ⟫} {x y : ⟪ A ⟫}
     → f R g → x R y → (f ⋅ x) R (g ⋅ y))
  (_⦉R⦊_⇰_ : ∀ {ℓ₁} ℓ₂ {A : Poset ℓ₁} → relation (ℓ₁ ⊔ᴸ ↑ᴸ ℓ₂) ⟪ A ⟫)
  (mk[⇰] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {x₁ x₂ : ⟪ A ⟫} → ℓ₂ ⦉ _R_ ⦊ x₁ ⇰ x₂ → ℓ₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭)
  (un[⇰] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {x₁ x₂ : ⟪ A ⟫} → ℓ₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → ℓ₂ ⦉ _R_ ⦊ x₁ ⇰ x₂)
  where
  open Logical[↗] _R_ res[fx][↗]

  [proof-mode]_∎ : ∀ {ℓ} {A : Poset ℓ} {x₁ x₂ : ⟪ A ⟫} → ℓ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → x₁ R x₂
  [proof-mode] F ∎ = un[⇰] F {k = id♮} (xRx {{R-Refl}})

  infixr 0  _‣_
  _‣_ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {x₁ x₂ x₃ : ⟪ A ⟫} → ℓ₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → ℓ₂ ⦉R⦊ ⟬ x₂ ⟭ ⇰ ⟬ x₃ ⟭ → ℓ₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₃ ⟭
  _‣_ G F = mk[⇰] $ λ {B} {y} {k} → un[⇰] G {k = k} ∘ un[⇰] F {k = k}

  [[_]] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} (x : ⟪ A ⟫) → ℓ₂ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ x ⟭
  [[ x ]] = mk[⇰] id

  ⟅_⟆ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {x₁ x₂ : ⟪ A ⟫} → x₁ R x₂ → ℓ₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
  ⟅ x₁Rx₂ ⟆ = mk[⇰] $ λ {B} {y} {k} P → _⊚_ {{R-Transitive}} P (res[•x][↗] {f = k} x₁Rx₂)

  ⟅_⟆⸢≡⸣ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} → {x₁ x₂ : ⟪ A ⟫} (P : x₁ ≡ x₂) → ℓ₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
  ⟅ x₁≡x₂ ⟆⸢≡⸣ = ⟅ xRx[≡] x₁≡x₂ ⟆

  [focus-in_] :
    ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Poset ℓ₁} {B : Poset ℓ₂} (op : ⟪ A ↗ B ⟫) {x : ⟪ A ⟫} {y : ⟪ A ⟫}
    → ℓ₃ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ y ⟭ → ℓ₃ ⦉R⦊ ⟬ op ⋅ x ⟭ ⇰ ⟬ op ⋅ y ⟭
  [focus-in op ] x⇰y = mk[⇰] $ λ {D} {z} {k} → un[⇰] x⇰y {k = k ∘♮ op}

  [focus-left_𝑜𝑓_] :
    ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} (op : ⟪ A ↗ B ↗ C ⟫) (z : ⟪ B ⟫) {x y : ⟪ A ⟫} 
    → ℓ₄ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ y ⟭ → ℓ₄ ⦉R⦊ ⟬ op ⋅ x ⋅ z ⟭ ⇰ ⟬ op ⋅ y ⋅ z ⟭
  [focus-left op 𝑜𝑓 z ] x⇰y = mk[⇰] $ λ {_ _ k} → un[⇰] x⇰y {k = k ∘♮ flip♮ ⋅ op ⋅ z}

  [focus-right_𝑜𝑓_] :
    ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Poset ℓ₁} {B : Poset ℓ₂} {C : Poset ℓ₃} (op : ⟪ A ↗ B ↗ C ⟫) (z : ⟪ A ⟫) {x y : ⟪ B ⟫}
    → ℓ₄ ⦉R⦊ ⟬ x ⟭ ⇰ ⟬ y ⟭ → ℓ₄ ⦉R⦊ ⟬ op ⋅ z ⋅ x ⟭ ⇰ ⟬ op ⋅ z ⋅ y ⟭
  [focus-right op 𝑜𝑓 z ] x⇰y = mk[⇰] $ λ {_ _ k} → un[⇰] x⇰y {k = k ∘♮ op ⋅ z}

  module §-Reflexive[≈]
    {{R-Refl[≈] : ∀ {ℓ} {A : Poset ℓ} → Reflexiveᴳ _≈♮_ (_R_ {A = A})}}
    where
    ⟅_⟆⸢≈⸣ : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} → {x₁ x₂ : ⟪ A ⟫} (P : x₁ ≈♮ x₂) → ℓ₂ ⦉R⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
    ⟅ x₁≈x₂ ⟆⸢≈⸣ = ⟅ xRxᴳ x₁≈x₂ ⟆

data _⦉⊑⦊_⇰_ {ℓ₁} ℓ₂ {A : Poset ℓ₁} : relation (ℓ₁ ⊔ᴸ ↑ᴸ ℓ₂) ⟪ A ⟫ where
  mk[⦉⊑⦊]-≡ : ∀ {x₁ x₂ x₃ x₄ : ⟪ A ⟫} → x₃ ≡ ⟬ x₁ ⟭ → x₄ ≡ ⟬ x₂ ⟭ → ℓ₂ ⦉ _⊑♮_ ⦊ x₁ ⇰ x₂ → ℓ₂ ⦉⊑⦊ x₃ ⇰ x₄

mk[⦉⊑⦊] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {x₁ x₂ : ⟪ A ⟫} → ℓ₂ ⦉ _⊑♮_ ⦊ x₁ ⇰ x₂ → ℓ₂ ⦉⊑⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
mk[⦉⊑⦊] = mk[⦉⊑⦊]-≡ ↯ ↯

un[⦉⊑⦊] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {x₁ x₂ : ⟪ A ⟫} → ℓ₂ ⦉⊑⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → ℓ₂ ⦉ _⊑♮_ ⦊ x₁ ⇰ x₂
un[⦉⊑⦊] (mk[⦉⊑⦊]-≡ E₁ E₂ P) {B} {y} {k} rewrite inj[⟬⟭] E₁ | inj[⟬⟭] E₂ = P {B} {y} {k}

module ProofMode[⊑] where
  open ProofMode _⊑♮_ res[fx][↗]⸢⊑⸣ _⦉⊑⦊_⇰_ mk[⦉⊑⦊] un[⦉⊑⦊] public
  open §-Reflexive[≈] public

open ProofMode[⊑] using () renaming
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

data _⦉≈⦊_⇰_ {ℓ₁} ℓ₂ {A : Poset ℓ₁} : relation (ℓ₁ ⊔ᴸ ↑ᴸ ℓ₂) ⟪ A ⟫ where
  mk[⦉≈⦊]-≡ : ∀ {x₁ x₂ x₃ x₄ : ⟪ A ⟫} → x₃ ≡ ⟬ x₁ ⟭ → x₄ ≡ ⟬ x₂ ⟭ → ℓ₂ ⦉ _≈♮_ ⦊ x₁ ⇰ x₂ → ℓ₂ ⦉≈⦊ x₃ ⇰ x₄

mk[⦉≈⦊] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {x₁ x₂ : ⟪ A ⟫} → ℓ₂ ⦉ _≈♮_ ⦊ x₁ ⇰ x₂ → ℓ₂ ⦉≈⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
mk[⦉≈⦊] = mk[⦉≈⦊]-≡ ↯ ↯

un[⦉≈⦊] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {x₁ x₂ : ⟪ A ⟫} → ℓ₂ ⦉≈⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → ℓ₂ ⦉ _≈♮_ ⦊ x₁ ⇰ x₂
un[⦉≈⦊] (mk[⦉≈⦊]-≡ E₁ E₂ P) {B} {y} {k} rewrite inj[⟬⟭] E₁ | inj[⟬⟭] E₂ = P {B} {y} {k}

module ProofMode[≈] where
  open ProofMode _≈♮_ res[fx][↗]⸢≈⸣ _⦉≈⦊_⇰_ mk[⦉≈⦊] un[⦉≈⦊] public
open ProofMode[≈] using () renaming
  ( [proof-mode]_∎    to [proof-mode]⸢≈⸣_∎
  ; _‣_                to _‣⸢≈⸣_
  ; [[_]]            to [[_]]⸢≈⸣
  ; ⟅_⟆              to ⟅_⟆⸢≈-≈⸣
  ; ⟅_⟆⸢≡⸣            to ⟅_⟆⸢≈-≡⸣
  ; [focus-in_]       to [focus-in_]⸢≈⸣
  ; [focus-left_𝑜𝑓_]  to [focus-left_𝑜𝑓_]⸢≈⸣
  ; [focus-right_𝑜𝑓_] to [focus-right_𝑜𝑓_]⸢≈⸣
  ) public

data _⦉≡⦊_⇰_ {ℓ₁} ℓ₂ {A : Poset ℓ₁} : relation (ℓ₁ ⊔ᴸ ↑ᴸ ℓ₂) ⟪ A ⟫ where
  mk[⦉≡⦊]-≡ : ∀ {x₁ x₂ x₃ x₄ : ⟪ A ⟫} → x₃ ≡ ⟬ x₁ ⟭ → x₄ ≡ ⟬ x₂ ⟭ → ℓ₂ ⦉ _≡_ ⦊ x₁ ⇰ x₂ → ℓ₂ ⦉≡⦊ x₃ ⇰ x₄

mk[⦉≡⦊] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {x₁ x₂ : ⟪ A ⟫} → ℓ₂ ⦉ _≡_ ⦊ x₁ ⇰ x₂ → ℓ₂ ⦉≡⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭
mk[⦉≡⦊] = mk[⦉≡⦊]-≡ ↯ ↯

un[⦉≡⦊] : ∀ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {x₁ x₂ : ⟪ A ⟫} → ℓ₂ ⦉≡⦊ ⟬ x₁ ⟭ ⇰ ⟬ x₂ ⟭ → ℓ₂ ⦉ _≡_ ⦊ x₁ ⇰ x₂
un[⦉≡⦊] (mk[⦉≡⦊]-≡ E₁ E₂ P) {B} {y} {k} rewrite inj[⟬⟭] E₁ | inj[⟬⟭] E₂ = P {B} {y} {k}

module ProofMode[≡] where
  open ProofMode _≡_ res[•xy] _⦉≡⦊_⇰_ mk[⦉≡⦊] un[⦉≡⦊] public
open ProofMode[≡] using () renaming
  ( [proof-mode]_∎     to [proof-mode]⸢≡⸣_∎
  ; _‣_                to _‣⸢≡⸣_
  ; [[_]]              to [[_]]⸢≡⸣
  ; ⟅_⟆                to ⟅_⟆⸢≡-≡⸣
  ; [focus-in_]        to [focus-in_]⸢≡⸣
  ; [focus-left_𝑜𝑓_]   to [focus-left_𝑜𝑓_]⸢≡⸣
  ; [focus-right_𝑜𝑓_]  to [focus-right_𝑜𝑓_]⸢≡⸣
  ) public
