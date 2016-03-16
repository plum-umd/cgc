module Prelude.Relations where

open import Prelude.Core

infixr 11 _⇉_

predicate : ∀ {ℓ} ℓ' → Set ℓ → Set (↑ᴸ ℓ' ⊔ᴸ ℓ)
predicate ℓ' A = A → Set ℓ'

relation : ∀ {ℓ} ℓ' → Set ℓ → Set (↑ᴸ ℓ' ⊔ᴸ ℓ)
relation ℓ' A = A → A → Set ℓ'

proper : ∀ {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) → A → Set ℓ'
proper _R_ x = x R x

_⇉_ : ∀ {ℓ₁ ℓ₁' ℓ₂ ℓ₂'} {A : Set ℓ₁} {B : Set ℓ₂} (_R₁_ : relation ℓ₁' A) (_R₂_ : relation ℓ₂' B) → relation (ℓ₁ ⊔ᴸ ℓ₁' ⊔ᴸ ℓ₂') (A → B)
(_R₁_ ⇉ _R₂_) f g = ∀ {x y} → x R₁ y → f x R₂ g y

reflexive : ∀ {ℓ ℓ'} {A : Set ℓ} → relation ℓ' A → Set (ℓ ⊔ᴸ ℓ')
reflexive _R_ = ∀ {x} → x R x

reflexive[_] : ∀ {ℓ ℓᵉ ℓʳ} {A : Set ℓ} → relation ℓᵉ A → relation ℓʳ A → Set (ℓ ⊔ᴸ ℓᵉ ⊔ᴸ ℓʳ)
reflexive[ _~_ ] _R_ = ∀ {x y} → x ~ y → x R y

transitive : ∀ {ℓ ℓ'} {A : Set ℓ} → relation ℓ' A → Set (ℓ ⊔ᴸ ℓ')
transitive _R_ = ∀ {x y z} → y R z → x R y → x R z

symmetric : ∀ {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) → Set (ℓ ⊔ᴸ ℓ')
symmetric _R_ = ∀ {x y} → x R y → y R x

antisymmetric : ∀ {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) → Set (ℓ ⊔ᴸ ℓ')
antisymmetric _R_ = ∀ {x y} → x R y → y R x → x ≡ y

antisymmetric[_] : ∀ {ℓ ℓᵉ ℓ'} {A : Set ℓ} (_~_ : relation ℓᵉ A) (_R_ : relation ℓ' A) → Set (ℓ ⊔ᴸ ℓᵉ ⊔ᴸ ℓ')
antisymmetric[ _~_ ] _R_ = ∀ {x y} → x R y → y R x → x ~ y

data total-ordering {ℓ ℓ' ℓ''} {A : Set ℓ} (_~_ : relation ℓ' A) (_R_ : relation ℓ'' A) (x y : A) : Set (ℓ ⊔ᴸ ℓ' ⊔ᴸ ℓ'') where
  [<] : x R y → not (y R x) → total-ordering _~_ _R_ x y
  [~] : x ~ y → total-ordering _~_ _R_ x y
  [>] : y R x → not (x R y) → total-ordering _~_ _R_ x y

dec-total-order : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} (_~_ : relation ℓ' A) (_R_ : relation ℓ'' A) → Set (ℓ ⊔ᴸ ℓ' ⊔ᴸ ℓ'')
dec-total-order _~_ _R_ = ∀ x y → total-ordering _~_ _R_ x y

data relationship {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) (x y : A) : Set ℓ' where
  Yes : x R y → relationship _R_ x y
  No : not (x R y) → relationship _R_ x y

data is-rel {ℓ ℓ'} {A : Set ℓ} {_R_ : relation ℓ' A} {x y : A} : relationship _R_ x y → Set ℓ' where
  ↯Rel : ∀ {p : x R y} → is-rel (Yes p)

data not-rel {ℓ ℓ'} {A : Set ℓ} {_R_ : relation ℓ' A} {x y : A} : relationship _R_ x y → Set ℓ' where
  ↯Rel : ∀ {p : not (x R y)} → not-rel (No p)

dec-rel : ∀ {ℓ ℓ'} {A : Set ℓ} (_R_ : relation ℓ' A) → Set (ℓ ⊔ᴸ ℓ')
dec-rel _R_ = ∀ x y → relationship _R_ x y

data predication {ℓ ℓ'} {A : Set ℓ} (P : predicate ℓ' A) (x : A) : Set ℓ' where
  Yes : P x → predication P x
  No : not (P x) → predication P x

data is-pred {ℓ ℓ'} {A : Set ℓ} {P : predicate ℓ' A} {x : A} : predication P x → Set ℓ' where
  ↯Pred : ∀ {p : P x} → is-pred (Yes p)

data not-pred {ℓ ℓ'} {A : Set ℓ} {P : predicate ℓ' A} {x : A} : predication P x → Set ℓ' where
  ↯Pred : ∀ {p : not (P x)} → not-pred (No p)

dec-pred : ∀ {ℓ ℓ'} {A : Set ℓ} (P : predicate ℓ' A) → Set (ℓ ⊔ᴸ ℓ')
dec-pred P = ∀ x → predication P x
