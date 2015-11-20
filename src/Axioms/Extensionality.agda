module Extensionality where

open import Core

Extensionality : ∀ {𝓁₁ 𝓁₂} (A : Set 𝓁₁) → (A → Set 𝓁₂) → Set (𝓁₁ l⊔ 𝓁₂)
Extensionality A B = ∀ {f₁ f₂ : ∀ (x : A) → B x} → (∀ {x} → f₁ x ≡ f₂ x) → f₁ ≡ f₂

Extensionality' : ∀ {𝓁₁ 𝓁₂} (A : Set 𝓁₁) → (A → Set 𝓁₂) → Set (𝓁₁ l⊔ 𝓁₂)
Extensionality' A B = ∀ {f₁ f₂ : ∀ {x : A} → B x} → (∀ {x} → f₁ {x} ≡ f₂ {x}) → (λ {x} → f₁ {x}) ≡ (λ {x} → f₂ {x})

postulate
  Πext : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : A → Set 𝓁₂} → Extensionality A B
  Πext' : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : A → Set 𝓁₂} → Extensionality' A B

ext : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} {f g : A → B} → (∀ {x} → f x ≡ g x) → f ≡ g
ext = Πext

ext' : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} {f g : ∀ {x : A} → B} → (∀ {x} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
ext' = Πext'
