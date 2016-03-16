module Poset.GaloisConnection.Classical where

open import Prelude
open import Poset.Poset
open import Poset.Fun
open import Poset.Power
open import Poset.ProofMode
open import Poset.Lib

infixr 11 _⇄_

record _⇄_ {ℓ} (A B : Poset ℓ) : Set (↑ᴸ ℓ) where
  field
    α[_] : ⟪ A ↗ B ⟫
    γ[_] : ⟪ B ↗ A ⟫
    extensive[_] : id♮ ⊑♮ γ[_] ∘♮ α[_]
    reductive[_] : α[_] ∘♮ γ[_] ⊑♮ id♮
open _⇄_ public

⟦extensive⟧ : ∀ {ℓ} {A B : Poset ℓ} {α : ⟪ A ↗ B ⟫} {γ : ⟪ B ↗ A ⟫} → id♮ ⊑♮ γ ∘♮ α ↔ (∀ {x} → x ⊑♮ γ ⋅ (α ⋅ x))
⟦extensive⟧ {A = A} {B} {α} {γ} = LHS , RHS
  where
    LHS : id♮ ⊑♮ γ ∘♮ α → ∀ {x} → x ⊑♮ γ ⋅ (α ⋅ x)
    LHS expansive = res[f]⸢⊑↗⸣ expansive
    RHS : (∀ {x} → x ⊑♮ γ ⋅ (α ⋅ x)) → id♮ ⊑♮ γ ∘♮ α
    RHS sound = ext⸢⊑↗⸣ sound

⟦reductive⟧ : ∀ {ℓ} {A B : Poset ℓ} {α : ⟪ A ↗ B ⟫} {γ : ⟪ B ↗ A ⟫} → α ∘♮ γ ⊑♮ id♮ ↔ (∀ {x♯} → α ⋅ (γ ⋅ x♯) ⊑♮ x♯)
⟦reductive⟧ {A = A} {B} {α} {γ} = LHS , RHS
  where
    LHS : α ∘♮ γ ⊑♮ id♮ → ∀ {x♯} → α ⋅ (γ ⋅ x♯) ⊑♮ x♯
    LHS contractive = res[f]⸢⊑↗⸣ contractive
    RHS : (∀ {x♯} → α ⋅ (γ ⋅ x♯) ⊑♮ x♯) → α ∘♮ γ ⊑♮ id♮
    RHS complete = ext⸢⊑↗⸣ complete

sound[_] : ∀ {ℓ} {A B : Poset ℓ} (A⇄B : A ⇄ B) → ∀ {x} → x ⊑♮ γ[ A⇄B ] ⋅ (α[ A⇄B ] ⋅ x)
sound[ A⇄B ] = π₁ ⟦extensive⟧ extensive[ A⇄B ]

complete[_] : ∀ {ℓ} {A B : Poset ℓ} (A⇄B : A ⇄ B) → ∀ {x♯} → α[ A⇄B ] ⋅ (γ[ A⇄B ] ⋅ x♯) ⊑♮ x♯
complete[ A⇄B ] = π₁ ⟦reductive⟧ reductive[ A⇄B ]
