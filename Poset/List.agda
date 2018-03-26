module Poset.List where

open import Prelude
open import Poset.Poset
open import Poset.Fun

data list♭ {ℓ} (A : Poset ℓ) : Set ℓ where
  [] : list♭ A
  _∷_ : ⟪ A ⟫ → list♭ A → list♭ A

module _ {ℓ} {A : Poset ℓ} where
  data _∈⊑ˡ♭_ : ⟪ A ⟫ → list♭ A → Set ℓ where
    Zero : ∀ {x y ys} → x ⊑♮ y → x ∈⊑ˡ♭ (y ∷ ys)
    Succ : ∀ {x y ys} → x ∈⊑ˡ♭ ys → x ∈⊑ˡ♭ (y ∷ ys)
  data _⊑ˡ♭_ : list♭ A → list♭ A → Set ℓ where
    [] : ∀ {ys} → [] ⊑ˡ♭ ys
    _∷_ : ∀ {x xs ys} → x ∈⊑ˡ♭ ys → xs ⊑ˡ♭ ys → (x ∷ xs) ⊑ˡ♭ ys

  weaken[⊑]ˡ♭ : ∀ {xs ys} x → xs ⊑ˡ♭ ys → xs ⊑ˡ♭ (x ∷ ys)
  weaken[⊑]ˡ♭ x [] = []
  weaken[⊑]ˡ♭ x (∈ˡ ∷ ⊑ˡ) = Succ ∈ˡ ∷ weaken[⊑]ˡ♭ x ⊑ˡ

  xRx⸢⊑ˡ♭⸣ : ∀ {xs} → xs ⊑ˡ♭ xs
  xRx⸢⊑ˡ♭⸣ {[]} = []
  xRx⸢⊑ˡ♭⸣ {x ∷ xs} = Zero xRx ∷ weaken[⊑]ˡ♭ x xRx⸢⊑ˡ♭⸣

  weaken[∈/L]ˡ♭ : ∀ {x y xs} → x ⊑♮ y → y ∈⊑ˡ♭ xs → x ∈⊑ˡ♭ xs
  weaken[∈/L]ˡ♭ ⊑₁ (Zero ⊑₂) = Zero (⊑₂ ⊚ ⊑₁)
  weaken[∈/L]ˡ♭ ⊑₁ (Succ ∈⊑₁) = Succ (weaken[∈/L]ˡ♭ ⊑₁ ∈⊑₁)

  weaken[∈/R]ˡ♭ : ∀ {x xs ys} → x ∈⊑ˡ♭ xs → xs ⊑ˡ♭ ys → x ∈⊑ˡ♭ ys
  weaken[∈/R]ˡ♭ (Zero x⊑y) (∈ ∷ ⊑) = weaken[∈/L]ˡ♭ x⊑y ∈
  weaken[∈/R]ˡ♭ (Succ ∈′) (∈ ∷ ⊑) = weaken[∈/R]ˡ♭ ∈′ ⊑

  _⊚⸢⊑ˡ♭⸣_ : ∀ {xs ys zs} → ys ⊑ˡ♭ zs → xs ⊑ˡ♭ ys → xs ⊑ˡ♭ zs
  ⊑₂ ⊚⸢⊑ˡ♭⸣ [] = []
  ⊑₂ ⊚⸢⊑ˡ♭⸣ (∈₁ ∷ ⊑₁) = weaken[∈/R]ˡ♭ ∈₁ ⊑₂ ∷ (⊑₂ ⊚⸢⊑ˡ♭⸣ ⊑₁)

  instance
    Reflexive[⊑ˡ♭] : Reflexive _⊑ˡ♭_
    Reflexive[⊑ˡ♭] = record { xRx = xRx⸢⊑ˡ♭⸣ }
    Transitive[⊑ˡ♭] : Transitive _⊑ˡ♭_
    Transitive[⊑ˡ♭] = record { _⊚_ = _⊚⸢⊑ˡ♭⸣_ }
    Precision[list♭] : Precision ℓ (list♭ A)
    Precision[list♭] = mk[Precision] _⊑ˡ♭_

  singleˡ♭ : ⟪ A ⟫ → list♭ A
  singleˡ♭ x = x ∷ []

  mon[single]ˡ♭ : proper (_⊑♮_ ⇉ _⊑ˡ♭_) singleˡ♭
  mon[single]ˡ♭ ⊑ˣ = Zero ⊑ˣ ∷ []

  _⧺ˡ♭_ : list♭ A → list♭ A → list♭ A
  [] ⧺ˡ♭ ys = ys
  (x ∷ xs) ⧺ˡ♭ ys = x ∷ (xs ⧺ˡ♭ ys)

  append[⧺/∈]ˡ♭ : ∀ {x xs} ys → x ∈⊑ˡ♭ xs → x ∈⊑ˡ♭ (xs ⧺ˡ♭ ys)
  append[⧺/∈]ˡ♭ ys (Zero ⊑₁) = Zero ⊑₁
  append[⧺/∈]ˡ♭ ys (Succ ∈₁) = Succ (append[⧺/∈]ˡ♭ ys ∈₁)

  prepend[⧺/∈]ˡ♭ : ∀ {x ys} xs → x ∈⊑ˡ♭ ys → x ∈⊑ˡ♭ (xs ⧺ˡ♭ ys)
  prepend[⧺/∈]ˡ♭ [] ∈₁ = ∈₁
  prepend[⧺/∈]ˡ♭ (⊑₁ ∷ xs) ∈₁ = Succ (prepend[⧺/∈]ˡ♭ xs ∈₁)

  prepend[⧺/⊑]ˡ♭ : ∀ {xs zs} ys → xs ⊑ˡ♭ zs → xs ⊑ˡ♭ (ys ⧺ˡ♭ zs)
  prepend[⧺/⊑]ˡ♭ ys [] = []
  prepend[⧺/⊑]ˡ♭ ys (∈₁ ∷ ⊑₁) = prepend[⧺/∈]ˡ♭ ys ∈₁ ∷ prepend[⧺/⊑]ˡ♭ ys ⊑₁

  mon[⧺]ˡ♭ : proper (_⊑ˡ♭_ ⇉ _⊑ˡ♭_ ⇉ _⊑ˡ♭_) _⧺ˡ♭_
  mon[⧺]ˡ♭ {.[]} {xs} [] ⊑₂ = prepend[⧺/⊑]ˡ♭ xs ⊑₂
  mon[⧺]ˡ♭ {x ∷ xs₁} {xs₂} (∈₁ ∷ ⊑₁) {ys₁} {ys₂} ⊑₂ = append[⧺/∈]ˡ♭ ys₂ ∈₁ ∷ mon[⧺]ˡ♭ ⊑₁ ⊑₂

  lr⧺ : ∀ {xs ys zs : list♭ A} → xs ⊑ˡ♭ zs → ys ⊑ˡ♭ zs → (xs ⧺ˡ♭ ys) ⊑ˡ♭ zs
  lr⧺ [] ⊑ʸ = ⊑ʸ
  lr⧺ (∈ˣ ∷ ⊑₀) ⊑ʸ = ∈ˣ ∷ lr⧺ ⊑₀ ⊑ʸ

  append[⧺/⊑]ˡ♭ : ∀ {xs ys : list♭ A} zs → xs ⊑ˡ♭ ys → xs ⊑ˡ♭ (ys ⧺ˡ♭ zs)
  append[⧺/⊑]ˡ♭ zs [] = []
  append[⧺/⊑]ˡ♭ zs (∈₀ ∷ ⊑₀) = append[⧺/∈]ˡ♭ zs ∈₀ ∷ append[⧺/⊑]ˡ♭ zs ⊑₀

list♮ : ∀ {ℓ} → Poset ℓ → Poset ℓ
list♮ A = ⇧ (list♭ A)

module _ {ℓ} {A : Poset ℓ} where
  join[]♭ : list♭ (list♮ A) → list♭ A
  join[]♭ [] = []
  join[]♭ (♮⟨ xs ⟩ ∷ xss) = xs ⧺ˡ♭ join[]♭ xss

  ∈join[]♭ : ∀ {xs : list♭ A} {xss : list♭ (list♮ A)} → ♮ xs ∈⊑ˡ♭ xss → xs ⊑ˡ♭ join[]♭ xss
  ∈join[]♭ {xs₁} {♮⟨ xs₂ ⟩ ∷ xss} (Zero ♮⟨ ⊑ₓ ⟩) = append[⧺/⊑]ˡ♭ (join[]♭ xss) ⊑ₓ
  ∈join[]♭ {xs₁} {♮⟨ xs₂ ⟩ ∷ xss} (Succ ∈ₓ) = prepend[⧺/⊑]ˡ♭ xs₂ (∈join[]♭ ∈ₓ)

  mon[join[]♭] : proper (_⊑_ ⇉ _⊑_) join[]♭
  mon[join[]♭] {[]} {[]} [] = []
  mon[join[]♭] {[]} {x ∷ y} [] = []
  mon[join[]♭] {♮⟨ xs ⟩ ∷ xss} {♮⟨ ys ⟩ ∷ yss} (Zero ♮⟨ ⊑ₓ ⟩ ∷ ⊑₀) = lr⧺ (append[⧺/⊑]ˡ♭ (join[]♭ yss) ⊑ₓ) (mon[join[]♭] ⊑₀)
  mon[join[]♭] {♮⟨ xs ⟩ ∷ xss} {♮⟨ ys ⟩ ∷ yss} (Succ ⊑ₓ ∷ ⊑₀) = lr⧺ (prepend[⧺/⊑]ˡ♭ ys (∈join[]♭ ⊑ₓ)) (mon[join[]♭] ⊑₀)


module _ {ℓ₁ ℓ₂} {A : Poset ℓ₁} {B : Poset ℓ₂} where
  map[]♭ : ⟪ A ↗ B ⟫ → list♭ A → list♭ B
  map[]♭ f [] = []
  map[]♭ f (x ∷ xs) = f ⋅ x ∷ map[]♭ f xs

  map∈ : ∀ {f g : ⟪ A ↗ B ⟫} {x : ⟪ A ⟫} {xs : list♭ A} → f ⊑♮ g → x ∈⊑ˡ♭ xs → f ⋅ x ∈⊑ˡ♭ map[]♭ g xs
  map∈ ⊑ᶠ (Zero ⊑₀) = Zero (res[fx][↗]⸢⊑⸣ ⊑ᶠ ⊑₀)
  map∈ ⊑ᶠ (Succ ∈₁) = Succ (map∈ ⊑ᶠ ∈₁)

  mon[map[]♭] : proper (_⊑♮_ ⇉ _⊑_ ⇉ _⊑_) map[]♭
  mon[map[]♭] ⊑ᶠ [] = []
  mon[map[]♭] {f} {g} ⊑ᶠ {x ∷ xs} {ys} (∈₀ ∷ ⊑₀) = map∈ ⊑ᶠ ∈₀ ∷ mon[map[]♭] ⊑ᶠ ⊑₀

