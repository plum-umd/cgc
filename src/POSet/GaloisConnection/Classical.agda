module POSet.GaloisConnection.Classical where

open import Prelude
open import POSet.POSet
open import POSet.Fun
open import POSet.Power
open import POSet.ProofMode
open import POSet.Lib

infixr 4 _⇄_
record _⇄_ {𝓁} (A B : POSet 𝓁) : Set (sucˡ 𝓁) where
  field
    α[_] : ⟪ A ⇒ B ⟫
    γ[_] : ⟪ B ⇒ A ⟫
    expansive[_] : id⁺ ⊑ γ[_] ⊙ α[_]
    contractive[_] : α[_] ⊙ γ[_] ⊑ id⁺
open _⇄_ public

expansive↔sound : ∀ {𝓁} {A B : POSet 𝓁} {α : ⟪ A ⇒ B ⟫} {γ : ⟪ B ⇒ A ⟫} → id⁺ ⊑ γ ⊙ α ↔ (∀ {x} → x ⊑ γ ⋅ (α ⋅ x))
expansive↔sound {A = A} {B} {α} {γ} = LHS , RHS
  where
    LHS : id⁺ ⊑ γ ⊙ α → ∀ {x} → x ⊑ γ ⋅ (α ⋅ x)
    LHS expansive = res-f[⇒]⸢⊑⸣ expansive
    RHS : (∀ {x} → x ⊑ γ ⋅ (α ⋅ x)) → id⁺ ⊑ γ ⊙ α
    RHS sound = ext[⇒]⸢⊑⸣ sound

contractive↔complete : ∀ {𝓁} {A B : POSet 𝓁} {α : ⟪ A ⇒ B ⟫} {γ : ⟪ B ⇒ A ⟫} → α ⊙ γ ⊑ id⁺ ↔ (∀ {x♯} → α ⋅ (γ ⋅ x♯) ⊑ x♯)
contractive↔complete {A = A} {B} {α} {γ} = LHS , RHS
  where
    LHS : α ⊙ γ ⊑ id⁺ → ∀ {x♯} → α ⋅ (γ ⋅ x♯) ⊑ x♯
    LHS contractive = res-f[⇒]⸢⊑⸣ contractive
    RHS : (∀ {x♯} → α ⋅ (γ ⋅ x♯) ⊑ x♯) → α ⊙ γ ⊑ id⁺
    RHS complete = ext[⇒]⸢⊑⸣ complete

sound[_] : ∀ {𝓁} {A B : POSet 𝓁} (A⇄B : A ⇄ B) → ∀ {x} → x ⊑ γ[ A⇄B ] ⋅ (α[ A⇄B ] ⋅ x)
sound[ A⇄B ] = π₁ expansive↔sound expansive[ A⇄B ]

complete[_] : ∀ {𝓁} {A B : POSet 𝓁} (A⇄B : A ⇄ B) → ∀ {x♯} → α[ A⇄B ] ⋅ (γ[ A⇄B ] ⋅ x♯) ⊑ x♯
complete[ A⇄B ] = π₁ contractive↔complete contractive[ A⇄B ]
