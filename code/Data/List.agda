module Data.List where

open import Core
open import Relations
open import Classes

infixr 5 _++⸢list⸣_
_++⸢list⸣_ : ∀ {𝓁} {A : Set 𝓁} → list A → list A → list A
[] ++⸢list⸣ ys = ys
(x ∷ xs) ++⸢list⸣ ys = x ∷ (xs ++⸢list⸣ ys)

left-unit[++⸢list⸣] : ∀ {𝓁} {A : Set 𝓁} (xs : list A) → [] ++⸢list⸣ xs ≡ xs
left-unit[++⸢list⸣] xs = ↯

right-unit[++⸢list⸣] : ∀ {𝓁} {A : Set 𝓁} (xs : list A) → xs ++⸢list⸣ [] ≡ xs
right-unit[++⸢list⸣] [] = ↯
right-unit[++⸢list⸣] (x ∷ xs) rewrite right-unit[++⸢list⸣] xs = ↯

associativity[++⸢list⸣] : ∀ {𝓁} {A : Set 𝓁} (xs ys zs : list A) → (xs ++⸢list⸣ ys) ++⸢list⸣ zs ≡ xs ++⸢list⸣ ys ++⸢list⸣ zs
associativity[++⸢list⸣] [] ys zs = ↯
associativity[++⸢list⸣] (x ∷ xs) ys zs rewrite associativity[++⸢list⸣] xs ys zs = ↯

instance
  Monoid[list] : ∀ {𝓁} {A : Set 𝓁} → Monoid (list A)
  Monoid[list] = record
    { null = []
    ; _++_ = _++⸢list⸣_
    ; left-unit[++] = left-unit[++⸢list⸣]
    ; right-unit[++] = right-unit[++⸢list⸣]
    ; associativity[++] = associativity[++⸢list⸣]
    }

map⸢list⸣ : ∀ {𝓁₁ 𝓁₂} {A : Set 𝓁₁} {B : Set 𝓁₂} → (A → B) → list A  → list B
map⸢list⸣ f [] = []
map⸢list⸣ f (x ∷ xs) = f x ∷ map⸢list⸣ f xs

unit[map⸢list⸣] : ∀ {𝓁} {A : Set 𝓁} (xs : list A) → map⸢list⸣ id xs ≡ xs
unit[map⸢list⸣] [] = ↯
unit[map⸢list⸣] (x ∷ xs) rewrite unit[map⸢list⸣] xs = ↯

homomorphic[map⸢list⸣] : ∀ {𝓁} {A B C : Set 𝓁} (g : B → C) (f : A → B) (xs : list A) → map⸢list⸣ (g ∘ f) xs ≡ (map⸢list⸣ g ∘ map⸢list⸣ f) xs
homomorphic[map⸢list⸣] g f [] = ↯
homomorphic[map⸢list⸣] g f (x ∷ xs) rewrite homomorphic[map⸢list⸣] g f xs = ↯

instance
  Functor[list] : ∀ {𝓁} → Functor (list {𝓁})
  Functor[list] = record
    { map = map⸢list⸣
    ; unit[map] = unit[map⸢list⸣]
    ; homomorphic[map] = homomorphic[map⸢list⸣]
    }

infix 8 _∈⸢list⸣_
data _∈⸢list⸣_ {𝓁} {A : Set 𝓁} : A → list A → Set 𝓁 where
  Zero : ∀ {x xs} → x ∈⸢list⸣ (x ∷ xs)
  Suc : ∀ {x₁ x₂ xs} → x₂ ∈⸢list⸣ xs → x₂ ∈⸢list⸣ (x₁ ∷ xs)

single⸢list⸣ : ∀ {𝓁} {A : Set 𝓁} → A → list A
single⸢list⸣ x = x ∷ []

x∈single⸢list⸣ : ∀ {𝓁} {A : Set 𝓁} (x : A) → x ∈⸢list⸣ single⸢list⸣ x
x∈single⸢list⸣ x = Zero

x∈xs⸢list⸣ : ∀ {𝓁} {A : Set 𝓁} (x : A) (xs ys : list A) → x ∈⸢list⸣ xs → x ∈⸢list⸣ (xs ++⸢list⸣ ys)
x∈xs⸢list⸣ x (.x ∷ xs) ys Zero = Zero
x∈xs⸢list⸣ x (x' ∷ xs) ys (Suc x∈xs) = Suc (x∈xs⸢list⸣ x xs ys x∈xs)

x∈ys⸢list⸣ : ∀ {𝓁} {A : Set 𝓁} (x : A) (xs ys : list A) → x ∈⸢list⸣ ys → x ∈⸢list⸣ (xs ++⸢list⸣ ys)
x∈ys⸢list⸣ x []        ys x∈ys = x∈ys
x∈ys⸢list⸣ x (x' ∷ xs) ys x∈ys = Suc (x∈ys⸢list⸣ x xs ys x∈ys)

x∈xs++ys→⨄⸢list⸣ : ∀ {𝓁} {A : Set 𝓁} (x : A) (xs ys : list A) → x ∈⸢list⸣ (xs ++⸢list⸣ ys) → x ∈⸢list⸣ xs ⨄ x ∈⸢list⸣ ys
x∈xs++ys→⨄⸢list⸣ x []        ys x∈xs∪ys       = Inr x∈xs∪ys
x∈xs++ys→⨄⸢list⸣ x (.x ∷ xs) ys Zero          = Inl Zero
x∈xs++ys→⨄⸢list⸣ x (x' ∷ xs) ys (Suc x∈xs∪ys) with x∈xs++ys→⨄⸢list⸣ x xs ys x∈xs∪ys
... | Inl x∈xs = Inl (Suc x∈xs)
... | Inr x∈ys = Inr x∈ys

_⊆⸢list⸣_ : ∀ {𝓁} {A : Set 𝓁} → list A → list A → Set 𝓁
xs ⊆⸢list⸣ ys = ∀ {x} → x ∈⸢list⸣ xs → x ∈⸢list⸣ ys

homomorphic[∈⸢list⸣] : ∀ {𝓁} {A B : Set 𝓁} {f : A → B} {xs x} → x ∈⸢list⸣ xs → f x ∈⸢list⸣ map f xs
homomorphic[∈⸢list⸣] Zero = Zero
homomorphic[∈⸢list⸣] (Suc x∈xs) = Suc (homomorphic[∈⸢list⸣] x∈xs)
