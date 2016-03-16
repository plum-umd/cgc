module Prelude.Data.List where

open import Prelude.Core
open import Prelude.Relations
open import Prelude.Classes

infix  14 _∈ˡ_
infixr 22 _⧺ˡ_

_⧺ˡ_ : ∀ {ℓ} {A : Set ℓ} → list A → list A → list A
[] ⧺ˡ ys = ys
(x ∷ xs) ⧺ˡ ys = x ∷ (xs ⧺ˡ ys)

left-unit[⧺ˡ] : ∀ {ℓ} {A : Set ℓ} (xs : list A) → [] ⧺ˡ xs ≡ xs
left-unit[⧺ˡ] xs = ↯

right-unit[⧺ˡ] : ∀ {ℓ} {A : Set ℓ} (xs : list A) → xs ⧺ˡ [] ≡ xs
right-unit[⧺ˡ] [] = ↯
right-unit[⧺ˡ] (x ∷ xs) rewrite right-unit[⧺ˡ] xs = ↯

associative[⧺ˡ] : ∀ {ℓ} {A : Set ℓ} (xs ys zs : list A) → (xs ⧺ˡ ys) ⧺ˡ zs ≡ xs ⧺ˡ ys ⧺ˡ zs
associative[⧺ˡ] [] ys zs = ↯
associative[⧺ˡ] (x ∷ xs) ys zs rewrite associative[⧺ˡ] xs ys zs = ↯

instance
  Monoid[list] : ∀ {ℓ} {A : Set ℓ} → Monoid (list A)
  Monoid[list] = record
    { null = []
    ; _⧺_ = _⧺ˡ_
    ; left-unit[⧺] = left-unit[⧺ˡ]
    ; right-unit[⧺] = right-unit[⧺ˡ]
    ; associative[⧺] = associative[⧺ˡ]
    }

mapˡ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → list A  → list B
mapˡ f [] = []
mapˡ f (x ∷ xs) = f x ∷ mapˡ f xs

unit[mapˡ] : ∀ {ℓ} {A : Set ℓ} (xs : list A) → mapˡ id xs ≡ xs
unit[mapˡ] [] = ↯
unit[mapˡ] (x ∷ xs) rewrite unit[mapˡ] xs = ↯

homomorphic[mapˡ] : ∀ {ℓ} {A B C : Set ℓ} (g : B → C) (f : A → B) (xs : list A) → mapˡ (g ∘ f) xs ≡ (mapˡ g ∘ mapˡ f) xs
homomorphic[mapˡ] g f [] = ↯
homomorphic[mapˡ] g f (x ∷ xs) rewrite homomorphic[mapˡ] g f xs = ↯

instance
  Functor[list] : ∀ {ℓ} → Functor (list {ℓ})
  Functor[list] = record
    { map = mapˡ
    ; unit[map] = unit[mapˡ]
    ; homomorphic[map] = homomorphic[mapˡ]
    }

data _∈ˡ_ {ℓ} {A : Set ℓ} : A → list A → Set ℓ where
  Zero : ∀ {x xs} → x ∈ˡ (x ∷ xs)
  Suc : ∀ {x₁ x₂ xs} → x₂ ∈ˡ xs → x₂ ∈ˡ (x₁ ∷ xs)

singleˡ : ∀ {ℓ} {A : Set ℓ} → A → list A
singleˡ x = x ∷ []

∈singleˡ : ∀ {ℓ} {A : Set ℓ} (x : A) → x ∈ˡ singleˡ x
∈singleˡ x = Zero

∈∪/ILˡ : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : list A) → x ∈ˡ xs → x ∈ˡ (xs ⧺ˡ ys)
∈∪/ILˡ x (.x ∷ xs) ys Zero = Zero
∈∪/ILˡ x (x' ∷ xs) ys (Suc x∈xs) = Suc (∈∪/ILˡ x xs ys x∈xs)

∈∪/IRˡ : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : list A) → x ∈ˡ ys → x ∈ˡ (xs ⧺ˡ ys)
∈∪/IRˡ x []        ys x∈ys = x∈ys
∈∪/IRˡ x (x' ∷ xs) ys x∈ys = Suc (∈∪/IRˡ x xs ys x∈ys)

∈∪/Eˡ : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : list A) → x ∈ˡ (xs ⧺ˡ ys) → x ∈ˡ xs ∨ x ∈ˡ ys
∈∪/Eˡ x []        ys x∈xs∪ys       = Inr x∈xs∪ys
∈∪/Eˡ x (.x ∷ xs) ys Zero          = Inl Zero
∈∪/Eˡ x (x' ∷ xs) ys (Suc x∈xs∪ys) with ∈∪/Eˡ x xs ys x∈xs∪ys
... | Inl x∈xs = Inl (Suc x∈xs)
... | Inr x∈ys = Inr x∈ys

_⊆ˡ_ : ∀ {ℓ} {A : Set ℓ} → list A → list A → Set ℓ
xs ⊆ˡ ys = ∀ {x} → x ∈ˡ xs → x ∈ˡ ys

instance
  FiniteSet[list] : ∀ {ℓ} → FiniteSet (list {ℓ})
  FiniteSet[list] = record
    { _∈_ = _∈ˡ_
    ; single = singleˡ
    ; _∪_ = _⧺_
    ; ∈single = ∈singleˡ
    ; ∈∪/IL = ∈∪/ILˡ
    ; ∈∪/IR = ∈∪/IRˡ
    ; ∈∪/E = ∈∪/Eˡ
    }
  
homomorphic[∈ˡ] : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {xs x} → x ∈ˡ xs → f x ∈ˡ map f xs
homomorphic[∈ˡ] Zero = Zero
homomorphic[∈ˡ] (Suc x∈xs) = Suc (homomorphic[∈ˡ] x∈xs)

-----------
-- Monad --
-----------

returnˡ : ∀ {ℓ} {A : Set ℓ} → A → list A
returnˡ x = x ∷ []

bindˡ : ∀ {ℓ} {A B : Set ℓ} → list A → (A → list B) → list B
bindˡ [] f = []
bindˡ (x ∷ xs) f = f x ⧺ bindˡ xs f

left-unit[bindˡ] : ∀ {ℓ} {A B : Set ℓ} (x : A) (f : A → list B) → bindˡ (returnˡ x) f ≡ f x
left-unit[bindˡ] x f rewrite right-unit[⧺] (f x) = ↯

right-unit[bindˡ] : ∀ {ℓ} {A : Set ℓ} (xM : list A) → bindˡ xM returnˡ ≡ xM
right-unit[bindˡ] [] = ↯
right-unit[bindˡ] (x ∷ xM) rewrite right-unit[bindˡ] xM = ↯

distributive[bindˡ] : ∀ {ℓ} {A B : Set ℓ} (xM₁ xM₂ : list A) (f : A → list B) → bindˡ (xM₁ ⧺ xM₂) f ≡ bindˡ xM₁ f ⧺ bindˡ xM₂ f
distributive[bindˡ] [] xM₂ f = ↯
distributive[bindˡ] (x ∷ xM₁) xM₂ f rewrite distributive[bindˡ] xM₁ xM₂ f | associative[⧺] (f x) (bindˡ xM₁ f) (bindˡ xM₂ f) = ↯

associative[bindˡ] : ∀ {ℓ} {A B C : Set ℓ} (xM : list A) (f : A → list B) (g : B → list C) → bindˡ (bindˡ xM f) g ≡ bindˡ xM (λ x → bindˡ (f x) g)
associative[bindˡ] [] f g = ↯
associative[bindˡ] (x ∷ xM) f g rewrite distributive[bindˡ] (f x) (bindˡ xM f) g | associative[bindˡ] xM f g = ↯
                                         
instance
  Monad[list] : ∀ {ℓ} → Monad {ℓ} list
  Monad[list] = record
    { return = returnˡ
    ; bind = bindˡ
    ; left-unit[bind] = left-unit[bindˡ]
    ; right-unit[bind] = right-unit[bindˡ]
    ; associative[bind] = associative[bindˡ]
    }
