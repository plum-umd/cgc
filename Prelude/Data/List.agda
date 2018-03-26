module Prelude.Data.List where

open import Prelude.Core
open import Prelude.Classes
open import Prelude.Orders

module _ {ℓ} {A : Set ℓ} where
  module _ {{_ : IEq A}} where
    data _≍ˡ_ : list A → list A → Set ℓ where
      [] : [] ≍ˡ []
      _∷_ : ∀ {x xs y ys} → x ≍ y → xs ≍ˡ ys → (x ∷ xs) ≍ˡ (y ∷ ys)

    sound[≍]ˡ : ∀ {xs ys} → xs ≍ˡ ys → xs ≡ ys
    sound[≍]ˡ [] = ↯
    sound[≍]ˡ (x≍y ∷ xs≍ys) rewrite sound[≍][ A ] x≍y | sound[≍]ˡ xs≍ys = ↯

    complete[≍]ˡ : ∀ {xs ys} → xs ≡ ys → xs ≍ˡ ys
    complete[≍]ˡ {[]} ↯ = []
    complete[≍]ˡ {x ∷ xs} ↯ = complete[≍][ A ] ↯ ∷ complete[≍]ˡ ↯

    data _≭ˡ_ : list A → list A → Set ℓ where
      ∷≭[] : ∀ {x xs} → (x ∷ xs) ≭ˡ []
      []≭∷ : ∀ {x xs} → [] ≭ˡ (x ∷ xs)
      Zero : ∀ {x xs y ys} → x ≭ y → (x ∷ xs) ≭ˡ (y ∷ ys)
      Succ : ∀ {x xs y ys} → xs ≭ˡ ys → (x ∷ xs) ≭ˡ (y ∷ ys)

    sound[≭]ˡ : ∀ {xs ys} → xs ≭ˡ ys → xs ≢ ys
    sound[≭]ˡ ∷≭[] ()
    sound[≭]ˡ []≭∷ ()
    sound[≭]ˡ (Zero x≭y) ↯ = sound[≭][ A ] x≭y ↯
    sound[≭]ˡ (Succ xs≭ys) ↯ = sound[≭]ˡ xs≭ys ↯

    instance
      IEq[list] : IEq (list A)
      IEq[list] = record
        { _≍_ = _≍ˡ_
        ; sound[≍] = sound[≍]ˡ
        ; complete[≍] = complete[≍]ˡ
        ; _≭_ = _≭ˡ_
        ; sound[≭] = sound[≭]ˡ
        }

_⧺ˡ_ : ∀ {ℓ} {A : Set ℓ} → list A → list A → list A
[] ⧺ˡ ys = ys
(x ∷ xs) ⧺ˡ ys = x ∷ (xs ⧺ˡ ys)

left-unit[⧺ˡ] : ∀ {ℓ} {A : Set ℓ} (xs : list A) → [] ⧺ˡ xs ≡ xs
left-unit[⧺ˡ] xs = ↯

right-unit[⧺ˡ] : ∀ {ℓ} {A : Set ℓ} (xs : list A) → xs ⧺ˡ [] ≡ xs
right-unit[⧺ˡ] [] = ↯
right-unit[⧺ˡ] (x ∷ xs) rewrite right-unit[⧺ˡ] xs = ↯

associative[⧺ˡ] : ∀ {ℓ} {A : Set ℓ} (xs ys zs : list A) → (xs ⧺ˡ ys) ⧺ˡ zs ≡ xs ⧺ˡ (ys ⧺ˡ zs)
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

homo[mapˡ] : ∀ {ℓ} {A B C : Set ℓ} (g : B → C) (f : A → B) (xs : list A) → mapˡ (g ∘ f) xs ≡ (mapˡ g ∘ mapˡ f) xs
homo[mapˡ] g f [] = ↯
homo[mapˡ] g f (x ∷ xs) rewrite homo[mapˡ] g f xs = ↯

instance
  Functor[list] : ∀ {ℓ} → Functor (list {ℓ})
  Functor[list] = record
    { map = mapˡ
    ; unit[map] = unit[mapˡ]
    ; homo[map] = homo[mapˡ]
    }

data _∈ˡ_ {ℓ} {A : Set ℓ} : A → list A → Set ℓ where
  Zero : ∀ {x xs} → x ∈ˡ (x ∷ xs)
  Succ : ∀ {x₁ x₂ xs} → x₂ ∈ˡ xs → x₂ ∈ˡ (x₁ ∷ xs)

singleˡ : ∀ {ℓ} {A : Set ℓ} → A → list A
singleˡ x = x ∷ []

∈singleˡ : ∀ {ℓ} {A : Set ℓ} (x : A) → x ∈ˡ singleˡ x
∈singleˡ x = Zero

∈∪/ILˡ : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : list A) → x ∈ˡ xs → x ∈ˡ (xs ⧺ˡ ys)
∈∪/ILˡ x (.x ∷ xs) ys Zero = Zero
∈∪/ILˡ x (x' ∷ xs) ys (Succ x∈xs) = Succ (∈∪/ILˡ x xs ys x∈xs)

∈∪/IRˡ : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : list A) → x ∈ˡ ys → x ∈ˡ (xs ⧺ˡ ys)
∈∪/IRˡ x []        ys x∈ys = x∈ys
∈∪/IRˡ x (x' ∷ xs) ys x∈ys = Succ (∈∪/IRˡ x xs ys x∈ys)

∈∪/Eˡ : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : list A) → x ∈ˡ (xs ⧺ˡ ys) → x ∈ˡ xs ∨ x ∈ˡ ys
∈∪/Eˡ x []        ys x∈xs∪ys       = Inr x∈xs∪ys
∈∪/Eˡ x (.x ∷ xs) ys Zero          = Inl Zero
∈∪/Eˡ x (x' ∷ xs) ys (Succ x∈xs∪ys) with ∈∪/Eˡ x xs ys x∈xs∪ys
... | Inl x∈xs = Inl (Succ x∈xs)
... | Inr x∈ys = Inr x∈ys

_⊆ˡ_ : ∀ {ℓ} {A : Set ℓ} → list A → list A → Set ℓ
xs ⊆ˡ ys = ∀ {x} → x ∈ˡ xs → x ∈ˡ ys

homo[∈ˡ] : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {xs x} → x ∈ˡ xs → f x ∈ˡ map f xs
homo[∈ˡ] Zero = Zero
homo[∈ˡ] (Succ x∈xs) = Succ (homo[∈ˡ] x∈xs)

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

---------------
-- Precision --
---------------

module _ {ℓ} {A : Set ℓ} {{_ : Precision ℓ A}} where
  data _∈⊑ˡ_ : A → list A → Set ℓ where
    Zero : ∀ {x y ys} → x ⊑ y → x ∈⊑ˡ (y ∷ ys)
    Succ : ∀ {x y ys} → x ∈⊑ˡ ys → x ∈⊑ˡ (y ∷ ys)
  data _⊑ˡ_ : list A → list A → Set ℓ where
    [] : ∀ {ys} → [] ⊑ˡ ys
    _∷_ : ∀ {x xs ys} → x ∈⊑ˡ ys → xs ⊑ˡ ys → (x ∷ xs) ⊑ˡ ys

  weaken[⊑]ˡ : ∀ {xs ys} x → xs ⊑ˡ ys → xs ⊑ˡ (x ∷ ys)
  weaken[⊑]ˡ x [] = []
  weaken[⊑]ˡ x (∈ˡ ∷ ⊑ˡ) = Succ ∈ˡ ∷ weaken[⊑]ˡ x ⊑ˡ

  xRx⸢⊑ˡ⸣ : ∀ {xs} → xs ⊑ˡ xs
  xRx⸢⊑ˡ⸣ {[]} = []
  xRx⸢⊑ˡ⸣ {x ∷ xs} = Zero xRx[⊑][ A ] ∷ weaken[⊑]ˡ x xRx⸢⊑ˡ⸣

  weaken[∈/L]ˡ : ∀ {x y xs} → x ⊑ y → y ∈⊑ˡ xs → x ∈⊑ˡ xs
  weaken[∈/L]ˡ ⊑₁ (Zero ⊑₂) = Zero (⊑₂ ⊚[⊑][ A ] ⊑₁)
  weaken[∈/L]ˡ ⊑₁ (Succ ∈⊑₁) = Succ (weaken[∈/L]ˡ ⊑₁ ∈⊑₁)

  weaken[∈/R]ˡ : ∀ {x xs ys} → x ∈⊑ˡ xs → xs ⊑ˡ ys → x ∈⊑ˡ ys
  weaken[∈/R]ˡ (Zero x⊑y) (∈ ∷ ⊑) = weaken[∈/L]ˡ x⊑y ∈
  weaken[∈/R]ˡ (Succ ∈′) (∈ ∷ ⊑) = weaken[∈/R]ˡ ∈′ ⊑

  _⊚⸢⊑ˡ⸣_ : ∀ {xs ys zs} → ys ⊑ˡ zs → xs ⊑ˡ ys → xs ⊑ˡ zs
  ⊑₂ ⊚⸢⊑ˡ⸣ [] = []
  ⊑₂ ⊚⸢⊑ˡ⸣ (∈₁ ∷ ⊑₁) = weaken[∈/R]ˡ ∈₁ ⊑₂ ∷ (⊑₂ ⊚⸢⊑ˡ⸣ ⊑₁)

  instance
    Reflexive[⊑ˡ] : Reflexive _⊑ˡ_
    Reflexive[⊑ˡ] = record { xRx = xRx⸢⊑ˡ⸣ }
    Transitive[⊑ˡ] : Transitive _⊑ˡ_
    Transitive[⊑ˡ] = record { _⊚_ = _⊚⸢⊑ˡ⸣_ }
    Precision[list] : Precision ℓ (list A)
    Precision[list] = mk[Precision] _⊑ˡ_

  mon[single]ˡ : proper (_⊑_ ⇉ _⊑ˡ_) singleˡ
  mon[single]ˡ ⊑ˣ = Zero ⊑ˣ ∷ []

  append[⧺/∈]ˡ : ∀ {x xs} ys → x ∈⊑ˡ xs → x ∈⊑ˡ (xs ⧺ ys)
  append[⧺/∈]ˡ ys (Zero ⊑₁) = Zero ⊑₁
  append[⧺/∈]ˡ ys (Succ ∈₁) = Succ (append[⧺/∈]ˡ ys ∈₁)

  prepend[⧺/∈]ˡ : ∀ {x ys} xs → x ∈⊑ˡ ys → x ∈⊑ˡ (xs ⧺ ys)
  prepend[⧺/∈]ˡ [] ∈₁ = ∈₁
  prepend[⧺/∈]ˡ (⊑₁ ∷ xs) ∈₁ = Succ (prepend[⧺/∈]ˡ xs ∈₁)

  prepend[⧺/⊑]ˡ : ∀ {xs zs} ys → xs ⊑ˡ zs → xs ⊑ˡ (ys ⧺ zs)
  prepend[⧺/⊑]ˡ ys [] = []
  prepend[⧺/⊑]ˡ ys (∈₁ ∷ ⊑₁) = prepend[⧺/∈]ˡ ys ∈₁ ∷ prepend[⧺/⊑]ˡ ys ⊑₁

  mon[⧺]ˡ : proper (_⊑ˡ_ ⇉ _⊑ˡ_ ⇉ _⊑ˡ_) _⧺ˡ_
  mon[⧺]ˡ {.[]} {xs} [] ⊑₂ = prepend[⧺/⊑]ˡ xs ⊑₂
  mon[⧺]ˡ {x ∷ xs₁} {xs₂} (∈₁ ∷ ⊑₁) {ys₁} {ys₂} ⊑₂ = append[⧺/∈]ˡ ys₂ ∈₁ ∷ mon[⧺]ˡ ⊑₁ ⊑₂
