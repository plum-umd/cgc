module Prelude.Data.FMap where

open import Prelude.Core
open import Prelude.Classes
open import Prelude.Orders
open import Prelude.Data.AddTop

-- infixr 11 _⇰_
-- infixr 11 ⇰[]
-- infixr 40 _⋄_⋄_∷_

module _ {ℓ ℓʳ} {K V : Set ℓ} {{_ : Order ℓʳ K}} where
  _⧺ᶠ[_]_ : list (K ∧ V) → (V → V → V) → list (K ∧ V) → list (K ∧ V)
  [] ⧺ᶠ[ _ ] kvs = kvs
  kvs ⧺ᶠ[ _ ] [] = kvs
  (⟨ k₁ , v₁ ⟩ ∷ kvs₁) ⧺ᶠ[ f ] (⟨ k₂ , v₂ ⟩ ∷ kvs₂) with k₁ ⋚ k₂
  … | [<] = ⟨ k₁ , v₁ ⟩ ∷ (kvs₁ ⧺ᶠ[ f ] (⟨ k₂ , v₂ ⟩ ∷ kvs₂))
  … | [≡] = ⟨ k₁ , f v₁ v₂ ⟩ ∷ (kvs₁ ⧺ᶠ[ f ] kvs₂) 
  … | [>] = ⟨ k₂ , v₂ ⟩ ∷ ((⟨ k₁ , v₁ ⟩ ∷ kvs₁) ⧺ᶠ[ f ] kvs₂)

  _⋇ᶠ[_]_ : list (K ∧ V) → (V → V → V) → list (K ∧ V) → list (K ∧ V)
  kvs ⋇ᶠ[ f ] [] = []
  [] ⋇ᶠ[ f ] kvs = []
  (⟨ k₁ , v₁ ⟩ ∷ kvs₁) ⋇ᶠ[ f ] (⟨ k₂ , v₂ ⟩ ∷ kvs₂) with k₁ ⋚ k₂
  … | [<] = kvs₁ ⋇ᶠ[ f ] (⟨ k₂ , v₂ ⟩ ∷ kvs₂)
  … | [≡] = ⟨ k₁ , f v₁ v₂ ⟩ ∷ (kvs₁ ⋇ᶠ[ f ] kvs₂)
  … | [>] = (⟨ k₁ , v₁ ⟩ ∷ kvs₁) ⋇ᶠ[ f ] kvs₂

  ❴_↦_❵ᶠ : K → V → list (K ∧ V)
  ❴ k ↦ v ❵ᶠ = ⟨ k , v ⟩ ∷ []

  _[_↦_]ᶠ : list (K ∧ V) → K → V → list (K ∧ V)
  kvs [ k ↦ v ]ᶠ = ❴ k ↦ v ❵ᶠ ⧺ᶠ[ const ] kvs

  _[_] : list (K ∧ V) → K → option V
  [] [ _ ] = None
  (⟨ k′ , v′ ⟩ ∷ kvs) [ k ] with k ⋚ k′
  … | [<] = None
  … | [≡] = Some v′
  … | [>] = kvs [ k ]

  _∈?_ : K → list (K ∧ V) → ‼
  k ∈? [] = ✗
  k ∈? (⟨ k′ , v′ ⟩ ∷ kvs) with k ⋚ k′
  … | [<] = ✗
  … | [≡] = ✓
  … | [>] = k ∈? kvs

  data _∈_ : K → list (K ∧ V) → Set where
    Zero : ∀ {k v kvs} → k ∈ (⟨ k , v ⟩ ∷ kvs)
    Succ : ∀ {k k′ v′ kvs} → k ∈ kvs → k ∈ (⟨ k′ , v′ ⟩ ∷ kvs)

  data _∉_ : K → list (K ∧ V) → Set ℓ where
    [] : ∀ {k} → k ∉ []
    _∷_ : ∀ {k k′ v′ kvs}
      → k ≢ k′
      → k ∉ kvs
      → k ∉ (⟨ k′ , v′ ⟩ ∷ kvs)

  data ⟨_↦_⟩∈_ : K → V → list (K ∧ V) → Set where
    Zero : ∀ {k v kvs} → ⟨ k ↦ v ⟩∈ (⟨ k , v ⟩ ∷ kvs)
    Succ : ∀ {k v k′ v′ kvs} → ⟨ k ↦ v ⟩∈ kvs → ⟨ k ↦ v ⟩∈ (⟨ k′ , v′ ⟩ ∷ kvs)

  sound[∉] : ∀ {k kvs} → k ∉ kvs → ¬ (k ∈ kvs)
  sound[∉] {k} {⟨ .k , v′ ⟩ ∷ kvs} (k≢k ∷ k∉kvs) Zero = k≢k ↯
  sound[∉] {k} {⟨ k′ , v′ ⟩ ∷ kvs} (k≢k′ ∷ k∉kvs) (Succ k∈kvs) = sound[∉] k∉kvs k∈kvs

  sound[↦∉] : ∀ {k v kvs} → k ∉ kvs → ¬ (⟨ k ↦ v ⟩∈ kvs)
  sound[↦∉] {k} {v} {⟨ .k , .v ⟩ ∷ kvs} (k≢k ∷ k∉kvs) Zero = k≢k ↯
  sound[↦∉] {k} {v} {⟨ k′ , v′ ⟩ ∷ kvs} (k≢k′ ∷ k∉kvs) (Succ k∈kvs) = sound[↦∉] k∉kvs k∈kvs

  data _∈!ᴾ_ (k : K) (kvs : list (K ∧ V)) : Set ℓ where
    ✓ : k ∈ kvs → k ∈!ᴾ kvs
    ✗ : k ∉ kvs → k ∈!ᴾ kvs

  data _∈!ᴸ_‖[_,_] (k : K) (kvs : list (K ∧ V)) : ‼ → k ∈!ᴾ kvs → Set where
    ✓ : ∀ {E : k ∈ kvs} → k ∈!ᴸ kvs ‖[ ✓ , ✓ E ]
    ✗ : ∀ {E : k ∉ kvs} → k ∈!ᴸ kvs ‖[ ✗ , ✗ E ]

  data _↦∈!ᴾ_ (k : K) (kvs : list (K ∧ V)) : Set ℓ where
    ✓ : ∀ {v} → ⟨ k ↦ v ⟩∈ kvs → k ↦∈!ᴾ kvs
    ✗ : k ∉ kvs → k ↦∈!ᴾ kvs

  data _↦∈!ᴸ_‖[_,_] (k : K) (kvs : list (K ∧ V)) : option V → k ↦∈!ᴾ kvs → Set ℓ where
    ✓ : ∀ {v} {E : ⟨ k ↦ v ⟩∈ kvs} → k ↦∈!ᴸ kvs ‖[ Some v , ✓ E ]
    ✗ : ∀ {E : k ∉ kvs} → k ↦∈!ᴸ kvs ‖[ None , ✗ E ]

  syntax ⊆[] _⊑_ kvs₁ kvs₂ = kvs₁ ⊆[ _⊑_ ] kvs₂
  data ⊆[] (_⊑_ : V → V → Set ℓ) : list (K ∧ V) → list (K ∧ V) → Set ℓ where
    [] : ∀ {kvs}
      → [] ⊆[ _⊑_ ] kvs
    _⋄_∷_ : ∀ {k v v′ kvs₁ kvs₂}
      → ⟨ k ↦ v′ ⟩∈ kvs₂
      → v ⊑ v′
      → kvs₁ ⊆[ _⊑_ ] kvs₂ → (⟨ k , v ⟩ ∷ kvs₁) ⊆[ _⊑_ ] kvs₂
  syntax ⊈[] _⊑_ kvs₁ kvs₂ = kvs₁ ⊈[ _⊑_ ] kvs₂
  data ⊈[] (_⊑_ : V → V → Set ℓ) : list (K ∧ V) → list (K ∧ V) → Set ℓ where
    Zero∉ : ∀ {k v kvs₁ kvs₂}
      → k ∉ kvs₂
      → ⟨ k , v ⟩ ∷ kvs₁ ⊈[ _⊑_ ] kvs₂
    Zero∈ : ∀ {k v v′ kvs₁ kvs₂}
      → ⟨ k ↦ v′ ⟩∈ kvs₂
      → ¬ (v ⊑ v′)
      → ⟨ k , v ⟩ ∷ kvs₁ ⊈[ _⊑_ ] kvs₂
    Succ : ∀ {k v kvs₁ kvs₂}
      → kvs₁ ⊈[ _⊑_ ] kvs₂
      → (⟨ k , v ⟩ ∷ kvs₁) ⊈[ _⊑_ ] kvs₂

  syntax ⊆!ᴾ[] _⊑_ kvs₁ kvs₂ = kvs₁ ⊆?ᴾ[ _⊑_ ] kvs₂
  data ⊆!ᴾ[] (_⊑_ : V → V → Set ℓ) (kvs₁ kvs₂ : list (K ∧ V)) : Set ℓ where
    ✓ : kvs₁ ⊆[ _⊑_ ] kvs₂ → kvs₁ ⊆?ᴾ[ _⊑_ ] kvs₂
    ✗ : kvs₂ ⊈[ _⊑_ ] kvs₂ → kvs₁ ⊆?ᴾ[ _⊑_ ] kvs₂

  syntax ⊆!ᴸ[] _⊑_ kvs₁ kvs₂ r rᴾ = kvs₁ ⊆?ᴸ[ _⊑_ ] kvs₂ ‖[ r , rᴾ ]
  data ⊆!ᴸ[] (_⊑_ : V → V → Set ℓ) (kvs₁ kvs₂ : list (K ∧ V)) : ‼ → kvs₁ ⊆?ᴾ[ _⊑_ ] kvs₂ → Set ℓ where
    ✓ : ∀ {E : kvs₁ ⊆[ _⊑_ ] kvs₂} → kvs₁ ⊆?ᴸ[ _⊑_ ] kvs₂ ‖[ ✓ , ✓ E ]
    ✗ : ∀ {E : kvs₂ ⊈[ _⊑_ ] kvs₂} → kvs₁ ⊆?ᴸ[ _⊑_ ] kvs₂ ‖[ ✗ , ✗ E ]

  data sorted : add-⊤ K → list (K ∧ V) → Set (ℓ ⊔ᴸ ℓʳ) where
    [] : sorted ⊤ []
    _∷_ : ∀ {b k v kvs} → ⟨ k ⟩ < b → sorted b kvs → sorted ⟨ k ⟩ (⟨ k , v ⟩ ∷ kvs)

  _<[_]‖[_,_] : ∀ {b} k kvs → ⟨ k ⟩ < b → sorted b kvs → k ∉ kvs
  k <[ []                ]‖[ k<b      , σ        ] = []
  k <[ ⟨ k′ , v′ ⟩ ∷ kvs ]‖[ ⟨ k<k′ ⟩ , k′<b ∷ σ ] = strict[<]/≡[ K ] k<k′ ∷ (k <[ kvs ]‖[ k′<b ⊚ ⟨ k<k′ ⟩ , σ ])

  sorted≤ : ∀ {b} k kvs → sorted b kvs → k ∈ kvs → b ≤ ⟨ k ⟩
  sorted≤ .k (⟨ k , v ⟩ ∷ kvs) (k<b ∷ σ) Zero = xRx
  sorted≤ k (⟨ k′ , v ⟩ ∷ kvs) (k′<b ∷ σ) (Succ ∈) = sorted≤ k kvs σ ∈ ⊚ weaken[≺] k′<b

  ↦→∈ : ∀ k v kvs → ⟨ k ↦ v ⟩∈ kvs → k ∈ kvs
  ↦→∈ k v (⟨ .k , .v ⟩ ∷ kvs) Zero = Zero
  ↦→∈ k v (⟨ k′ , v′ ⟩ ∷ kvs) (Succ ∈₀) = Succ (↦→∈ k v kvs ∈₀)

  uniq : ∀ {k v₁ v₂ b kvs} → sorted b kvs → ⟨ k ↦ v₁ ⟩∈ kvs → ⟨ k ↦ v₂ ⟩∈ kvs → v₁ ≡ v₂
  uniq σ Zero Zero = ↯
  uniq {k} {_} {_} {_} {⟨ .k , v ⟩ ∷ kvs} (<₁ ∷ σ) Zero (Succ ↦₂) = exfalso (sound[↦∉] (k <[ kvs ]‖[ <₁ , σ ]) ↦₂)
  uniq {k} {_} {_} {_} {⟨ .k , v ⟩ ∷ kvs} (<₁ ∷ σ) (Succ ↦₁) Zero = exfalso (sound[↦∉] (k <[ kvs ]‖[ <₁ , σ ]) ↦₁)
  uniq (<₁ ∷ σ) (Succ ↦₁) (Succ ↦₂) = uniq σ ↦₁ ↦₂

  movealong : ∀ {k v kvs₁ kvs₂ _⊑_} → kvs₁ ⊆[ _⊑_ ] (⟨ k , v ⟩ ∷ kvs₂) → k ∉ kvs₁ → kvs₁ ⊆[ _⊑_ ] kvs₂
  movealong [] ∉₁ = []
  movealong (Zero ⋄ ⊑₁ ∷ ⊆₁) (≢₁ ∷ ∉₁) = exfalso (≢₁ ↯)
  movealong {k} {v} (Succ ∈₁ ⋄ ⊑₁ ∷ ⊆₁) (≢₁ ∷ ∉₁) = ∈₁ ⋄ ⊑₁ ∷ movealong ⊆₁ ∉₁

  extᶠ : ∀ {b₁} kvs₁ {b₂} kvs₂ _⊑_ {{_ : Antisymmetric _⊑_}} → sorted b₁ kvs₁ → sorted b₂ kvs₂ → kvs₁ ⊆[ _⊑_ ] kvs₂ → kvs₂ ⊆[ _⊑_ ] kvs₁ → kvs₁ ≡ kvs₂
  extᶠ .[] .[] _⊑_ σ₁ σ₂ [] [] = ↯
  extᶠ .[] (⟨ k₂ , v₂ ⟩ ∷ kvs₂) _⊑_ σ₁ σ₂ [] (() ⋄ ⊑₂ ∷ ⊆₂)
  extᶠ (⟨ k₁ , v₁ ⟩ ∷ kvs₁) .[] _⊑_ σ₁ σ₂ (() ⋄ ⊑₁ ∷ ⊆₁) []
  extᶠ (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) _⊑_ (<₁ ∷ σ₁) (<₂ ∷ σ₂) (∈₁ ⋄ ⊑₁ ∷ ⊆₁) (∈₂ ⋄ ⊑₂ ∷ ⊆₂) with k₁ ⋚ᴾ k₂
  … | [<] <₁₂ = exfalso (sound[↦∉] (k₁ <[ ⟨ k₂ , v₂ ⟩ ∷ kvs₂ ]‖[ ⟨ <₁₂ ⟩ , <₂ ∷ σ₂ ]) ∈₁)
  … | [>] >₁₂ = exfalso (sound[↦∉] (k₂ <[ ⟨ k₁  , v₁ ⟩ ∷ kvs₁ ]‖[ ⟨ >₁₂ ⟩ , <₁ ∷ σ₁ ]) ∈₂)
  … | [≡] ≡₁₂ rewrite
      ≡₁₂ | uniq (<₁ ∷ σ₁) ∈₂ Zero | uniq (<₂ ∷ σ₂) ∈₁ Zero | ⋈ ⊑₁ ⊑₂
    | extᶠ kvs₁ kvs₂ _⊑_ σ₁ σ₂ (movealong ⊆₁ (k₂ <[ kvs₁ ]‖[ <₁ , σ₁ ])) (movealong ⊆₂ (k₂ <[ kvs₂ ]‖[ <₂ , σ₂ ])) = ↯

  sound[⊆] : ∀ {kvs₁ kvs₂ _⊑_} → kvs₁ ⊆[ _⊑_ ] kvs₂ → ∀ {k v} → ⟨ k ↦ v ⟩∈ kvs₁ → ∃ v′ 𝑠𝑡 ⟨ k ↦ v′ ⟩∈ kvs₂ ∧ v ⊑ v′
  sound[⊆] (_⋄_∷_ {k} {v} {v′} k↦v′ v⊑v′ ⊆₀) Zero = ⟨∃ v′ , ⟨ k↦v′ , v⊑v′ ⟩ ⟩
  sound[⊆] (_⋄_∷_ {k} {v} {v′} k↦v′ v⊑v′ ⊆₀) (Succ k↦v) = sound[⊆] ⊆₀ k↦v

  complete[⊆] : ∀ kvs₁ kvs₂ _⊑_ → (∀ {k v} → ⟨ k ↦ v ⟩∈ kvs₁ → ∃ v′ 𝑠𝑡 ⟨ k ↦ v′ ⟩∈ kvs₂ ∧ v ⊑ v′) → kvs₁ ⊆[ _⊑_ ] kvs₂
  complete[⊆] [] kvs₂ _⊑_ F = []
  complete[⊆] (⟨ k , v ⟩ ∷ kvs₁) kvs₂ _⊑_ F with F Zero
  … | ⟨∃ v′ , ⟨ k↦v′ , v⊑v′ ⟩ ⟩ = k↦v′ ⋄ v⊑v′ ∷ (complete[⊆] kvs₁ kvs₂ _⊑_ (λ k↦v → F (Succ k↦v)))

  data ∈∨ (f : V → V → V) k v kvs₁ kvs₂ : Set ℓ where
    Inl : ⟨ k ↦ v ⟩∈ kvs₁ → k ∉ kvs₂ → ∈∨ f k v kvs₁ kvs₂
    Inr : ⟨ k ↦ v ⟩∈ kvs₂ → k ∉ kvs₁ → ∈∨ f k v kvs₁ kvs₂
    Inlr : ∀ v₁ v₂ → ⟨ k ↦ v₁ ⟩∈ kvs₁ → ⟨ k ↦ v₂ ⟩∈ kvs₂ → v ≡ f v₁ v₂ → ∈∨ f k v kvs₁ kvs₂

  left-unit[⧺]ᶠ : ∀ f kvs → [] ⧺ᶠ[ f ] kvs ≡ kvs
  left-unit[⧺]ᶠ f kvs₁ = ↯

  right-unit[⧺]ᶠ : ∀ f kvs → kvs ⧺ᶠ[ f ] [] ≡ kvs
  right-unit[⧺]ᶠ f [] = ↯
  right-unit[⧺]ᶠ f (kv ∷ kvs) = ↯

  ∈∨! : ∀ {b₁ b₂} f k v kvs₁ kvs₂ → sorted b₁ kvs₁ → sorted b₂ kvs₂ → ⟨ k ↦ v ⟩∈ (kvs₁ ⧺ᶠ[ f ] kvs₂) → ∈∨ f k v kvs₁ kvs₂
  ∈∨! f k v [] kvs₂ σ₁ σ₂ ∈₀ = Inr ∈₀ []
  ∈∨! f k v kvs₁ [] σ₁ σ₂ ∈₀ rewrite right-unit[⧺]ᶠ f kvs₁ = Inl ∈₀ []
  ∈∨! f k v (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) σ₁ σ₂ ∈₀ with k₁ ⋚ k₂ | k₁ ⋚ᴾ k₂ | k₁ ⋚ᴸ k₂
  ∈∨! f k v (⟨ .k , .v ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (k₁<b₁ ∷ σ₁) (k₂<b₂ ∷ σ₂) Zero | [<] | [<] 1<2 | [<] = Inl Zero (k <[ ⟨ k₂ , v₂ ⟩ ∷ kvs₂ ]‖[ ⟨ 1<2 ⟩ , k₂<b₂ ∷ σ₂ ])
  ∈∨! f k v (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (k₁<b₁ ∷ σ₁) (k₂<b₂ ∷ σ₂) (Succ ∈₀) | [<] | [<] 1<2 | [<] with ∈∨! f k v kvs₁ (⟨ k₂ , v₂ ⟩ ∷ kvs₂) σ₁ (k₂<b₂ ∷ σ₂) ∈₀
  … | Inl ∈₁ ∉₂ = Inl (Succ ∈₁) ∉₂
  … | Inr ∈₂ ∉₁ = Inr ∈₂ (E ∷ {!!})
    where
      E : k ≢  k₁
      E ≡₀ with strict[≺][ _≤⸢add-⊤⸣_  , _<⸢add-⊤⸣_ ] {⟨ k₁ ⟩} {⟨ k ⟩}
      … | F rewrite ≡₀ = F {!!} {!!}
      -- {- {! λ k≡k₁ → strict[≺] (extend[≺]/R ⟨ 1<2 ⟩ (sorted≤ k (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (k₂<b₂ ∷ σ₂) (↦→∈ _ _ _ ∈₂))) (◇ k≡k₁)!} -} ∷ {!!}) -- {!!}
  … | Inlr v₁′ v₂′ ∈₁ ∈₂ ≡₁₂ = {!!}
  ∈∨! f k v (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (k₁<b₁ ∷ σ₁) (k₂<b₂ ∷ σ₂) ∈₀ | [≡] | [≡] 1≡2 | [≡] = {!!}
  ∈∨! f k v (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (k₁<b₁ ∷ σ₁) (k₂<b₂ ∷ σ₂) ∈₀ | [>] | [>] 1>2 | [>] = {!!}

  associative[⧺]ᶠ : ∀ f kvs₁ kvs₂ kvs₃ → (∀ x y z → f (f x y) z ≡ f x (f y z)) → (kvs₁ ⧺ᶠ[ f ] kvs₂) ⧺ᶠ[ f ] kvs₃ ≡ kvs₁ ⧺ᶠ[ f ] (kvs₂ ⧺ᶠ[ f ] kvs₃)
  associative[⧺]ᶠ f [] kvs₂ kvs₃ assoc[f] = ↯
  associative[⧺]ᶠ f kvs₁ [] kvs₃ assoc[f] rewrite right-unit[⧺]ᶠ f kvs₁ = ↯
  associative[⧺]ᶠ f kvs₁ kvs₂ [] assoc[f] rewrite right-unit[⧺]ᶠ f (kvs₁ ⧺ᶠ[ f ] kvs₂) | right-unit[⧺]ᶠ f kvs₂ = ↯
  associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f]
    with k₁ ⋚ᴾ k₂ | k₂ ⋚ᴾ k₃
  associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f] | [<] 1<2 | [<] 2<3
    rewrite ⋚[<] k₁ k₂ 1<2 | ⋚[<] k₂ k₃ 2<3 = {!!}
  associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f] | [<] 1<2 | [≡] 2≡3 = {!!}
  associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f] | [<] 1<2 | [>] 2>3 = {!!}
  associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f] | [≡] 1<2 | [<] 2<3 = {!!}
  associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f] | [≡] 1<2 | [≡] 2≡3 = {!!}
  associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f] | [≡] 1<2 | [>] 2>3 = {!!}
  associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f] | [>] 1<2 | [<] 2<3 = {!!}
  associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f] | [>] 1<2 | [≡] 2≡3 = {!!}
  associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f] | [>] 1<2 | [>] 2>3 = {!!}
  -- associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f] with k₁ ⋚ᴾ k₂ | k₁ ⋚ᴾ k₃ | k₂ ⋚ᴾ k₃
  -- … | [<] 1<2 | [<] 1<3 | [<] 2<3
  --   rewrite ⋚[<] k₁ k₂ 1<2 | ⋚[<] k₂ k₃ 2<3 | ⋚[<] k₁ k₃ 1<3 | ⋚[<] k₁ k₂ 1<2
  --   | associative[⧺]ᶠ f kvs₁ (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f]
  --   | ⋚[<] k₂ k₃ 2<3 = ↯
  -- … | [<] 1<2 | [<] 1<3 | [≡] 2≡3
  --   rewrite 2≡3 | ⋚[<] k₁ k₃ 1<3 | ⋚[≡] k₃ k₃ ↯ | ⋚[<] k₁ k₃ 1<3
  --   | associative[⧺]ᶠ f kvs₁ (⟨ k₃ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f]
  --   | ⋚[≡] k₃ k₃ ↯ = ↯
  -- … | [<] 1<2 | [<] 1<3 | [>] 2>3
  --   rewrite ⋚[<] k₁ k₂ 1<2 | ⋚[>] k₂ k₃ 2>3 | ⋚[<] k₁ k₃ 1<3
  --   | associative[⧺]ᶠ f kvs₁ (⟨ k₂ , v₂ ⟩ ∷ kvs₂) (⟨ k₃ , v₃ ⟩ ∷ kvs₃) assoc[f]
  --   | ⋚[>] k₂ k₃ 2>3 = ↯
  -- … | [<] 1<2 | [≡] 1≡3 | [<] 2<3 rewrite 1≡3 = exfalso (¬◇[<][ K ] 2<3 1<2)
  -- … | [<] 1<2 | [≡] 1≡3 | [≡] 2≡3 rewrite 1≡3 | 2≡3 = exfalso (¬xRx[<][ K ] 1<2)
  -- … | [<] 1<2 | [≡] 1≡3 | [>] 2>3
  --   rewrite 1≡3 | ⋚[<] k₃ k₂ 1<2 | ⋚[>] k₂ k₃ 2>3 | ⋚[≡] k₃ k₃ ↯
  --   | associative[⧺]ᶠ f kvs₁ (⟨ k₂ , v₂ ⟩ ∷ kvs₂) kvs₃ assoc[f] = ↯
  -- … | [<] 1<2 | [>] 1>3 | [<] 2<3 = exfalso (¬xRx[<][ K ] (1>3 ⊚[<][ K ] 2<3 ⊚[<][ K ] 1<2))
  -- … | [<] 1<2 | [>] 1>3 | [≡] 2≡3 rewrite 2≡3 = exfalso (¬◇[<][ K ] 1<2 1>3)
  -- … | [<] 1<2 | [>] 1>3 | [>] 2>3
  --   rewrite ⋚[<] k₁ k₂ 1<2 | ⋚[>] k₂ k₃ 2>3 | ⋚[>] k₁ k₃ 1>3
  --   | ◇ (associative[⧺]ᶠ f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) kvs₃ assoc[f])
  --   | ⋚[<] k₁ k₂ 1<2
  --   = ↯
  -- … | _ | _ | _ = {!!}

  commutative[⧺ᶠ] : ∀ f kvs₁ kvs₂ → (∀ x y → f x y ≡ f y x) → kvs₁ ⧺ᶠ[ f ] kvs₂ ≡ kvs₂ ⧺ᶠ[ f ] kvs₁
  commutative[⧺ᶠ] f [] kvs₂ comm[f] rewrite right-unit[⧺]ᶠ f kvs₂ = ↯
  commutative[⧺ᶠ] f kvs₁ [] comm[f] rewrite right-unit[⧺]ᶠ f kvs₁ = ↯
  commutative[⧺ᶠ] f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) (⟨ k₂ , v₂ ⟩ ∷ kvs₂) comm[f] with k₁ ⋚ k₂ | k₁ ⋚ᴾ k₂ | k₁ ⋚ᴸ k₂
  … | [<] | [<] 1<2 | [<] rewrite ⋚[>] k₂ k₁ 1<2 | commutative[⧺ᶠ] f kvs₁ (⟨ k₂ , v₂ ⟩ ∷ kvs₂) comm[f] = ↯
  … | [≡] | [≡] 1≡2 | [≡] rewrite 1≡2 | ⋚[≡] k₂ k₂ ↯ | comm[f] v₁ v₂ | commutative[⧺ᶠ] f kvs₁ kvs₂ comm[f] = ↯
  … | [>] | [>] 1>2 | [>] rewrite ⋚[<] k₂ k₁ 1>2 | commutative[⧺ᶠ] f (⟨ k₁ , v₁ ⟩ ∷ kvs₁) kvs₂ comm[f] = ↯

  ↦∈[⧺]/LR : ∀ {b₁ b₂} k v₁ v₂ f kvs₁ kvs₂ → sorted b₁ kvs₁ → sorted b₂ kvs₂ → ⟨ k ↦ v₁ ⟩∈ kvs₁ → ⟨ k ↦ v₂ ⟩∈ kvs₂ → ⟨ k ↦ f v₁ v₂ ⟩∈ (kvs₁ ⧺ᶠ[ f ] kvs₂)
  ↦∈[⧺]/LR k v₁ v₂ f (⟨ .k , .v₁ ⟩ ∷ kvs₁) (⟨ .k , .v₂ ⟩ ∷ kvs₂) (_ ∷ σ₁) (_ ∷ σ₂) Zero Zero rewrite ⋚[≡] k k ↯ = Zero
  ↦∈[⧺]/LR k v₁ v₂ f (⟨ .k , .v₁ ⟩ ∷ kvs₁) (⟨ k′ , v′ ⟩ ∷ kvs₂) (k<b₁ ∷ σ₁) (k′<b₂ ∷ σ₂) Zero (Succ ∈₂) with k ⋚ k′ | k ⋚ᴾ k′ | k ⋚ᴸ k′
  … | [<] | [<] k<k′ | [<] = exfalso (sound[↦∉] (k <[ kvs₂ ]‖[ k′<b₂ ⊚ ⟨ k<k′ ⟩ , σ₂ ]) ∈₂)
  … | [≡] | [≡] k≡k′ | [≡] rewrite k≡k′ = exfalso (sound[↦∉] (k′ <[ kvs₂ ]‖[ k′<b₂ , σ₂ ]) ∈₂)
  … | [>] | [>] k>k′ | [>] = Succ (↦∈[⧺]/LR k v₁ v₂ f (⟨ k , v₁ ⟩ ∷ kvs₁) kvs₂ (k<b₁ ∷ σ₁) σ₂ Zero ∈₂)
  ↦∈[⧺]/LR k v₁ v₂ f (⟨ k′ , v′ ⟩ ∷ kvs₁) (⟨ .k , .v₂ ⟩ ∷ kvs₂) (k′<b₁ ∷ σ₁) (k′<b₂ ∷ σ₂) (Succ ∈₁) Zero with k′ ⋚ k | k′ ⋚ᴾ k | k′ ⋚ᴸ k
  … | [<] | [<] k′<k | [<] = Succ (↦∈[⧺]/LR k v₁ v₂ f kvs₁ (⟨ k , v₂ ⟩ ∷ kvs₂) σ₁ (k′<b₂ ∷ σ₂) ∈₁ Zero)
  … | [≡] | [≡] k′≡k | [≡] rewrite k′≡k = exfalso (sound[↦∉] (k <[ kvs₁ ]‖[ k′<b₁ , σ₁ ]) ∈₁)
  … | [>] | [>] k′>k | [>] = exfalso (sound[↦∉] (k <[ kvs₁ ]‖[ k′<b₁ ⊚ ⟨ k′>k ⟩ , σ₁ ]) ∈₁)
  ↦∈[⧺]/LR k v₁ v₂ f (⟨ k₁′ , v₁′ ⟩ ∷ kvs₁) (⟨ k₂′ , v₂′ ⟩ ∷ kvs₂) (k′<b₁ ∷ σ₁) (k′<b₂ ∷ σ₂) (Succ ∈₁) (Succ ∈₂) with k₁′ ⋚ k₂′ | k₁′ ⋚ᴾ k₂′ | k₁′ ⋚ᴸ k₂′
  … | [<] | [<] k′<k | [<] = Succ (↦∈[⧺]/LR k v₁ v₂ f kvs₁ (⟨ k₂′ , v₂′ ⟩ ∷ kvs₂) σ₁ (k′<b₂ ∷ σ₂) ∈₁ (Succ ∈₂))
  … | [≡] | [≡] k′≡k | [≡] rewrite k′≡k = Succ (↦∈[⧺]/LR k v₁ v₂ f kvs₁ kvs₂ σ₁ σ₂ ∈₁ ∈₂)
  … | [>] | [>] k′>k | [>] = Succ (↦∈[⧺]/LR k v₁ v₂ f (⟨ k₁′ , v₁′ ⟩ ∷ kvs₁) kvs₂ (k′<b₁ ∷ σ₁) σ₂ (Succ ∈₁) ∈₂)

  ↦∈[⧺]/L : ∀ {b₁ b₂} k v f kvs₁ kvs₂ → sorted b₁ kvs₁ → sorted b₂ kvs₂ → ⟨ k ↦ v ⟩∈ kvs₁ → k ∉ kvs₂ → ⟨ k ↦ v ⟩∈ (kvs₁ ⧺ᶠ[ f ] kvs₂)
  ↦∈[⧺]/L k v f (⟨ .k , .v ⟩ ∷ kvs₁) .[] σ₁ σ₂ Zero [] = Zero
  ↦∈[⧺]/L k v f (⟨ .k , .v ⟩ ∷ kvs₁) (⟨ k′ , v′ ⟩ ∷ kvs₂) σ₁ (k′<b₂ ∷ σ₂) Zero (k≢k′ ∷ ∉₂) with k ⋚ k′ | k ⋚ᴾ k′ | k ⋚ᴸ k′
  … | [<] | [<] k′<k | [<] = Zero
  … | [≡] | [≡] k′≡k | [≡] rewrite k′≡k = exfalso (k≢k′ ↯)
  … | [>] | [>] k′>k | [>] = Succ (↦∈[⧺]/L k v f (⟨ k , v ⟩ ∷ kvs₁) kvs₂ σ₁ σ₂ Zero ∉₂)
  ↦∈[⧺]/L k v f (⟨ k′ , v′ ⟩ ∷ kvs₁) .[] (k′<b₁ ∷ σ₁) σ₂ (Succ ∈₁) [] = Succ ∈₁
  ↦∈[⧺]/L k v f (⟨ k₁′ , v₁′ ⟩ ∷ kvs₁) (⟨ k₂′ , v₂′ ⟩ ∷ kvs₂) (k₁′<b₁ ∷ σ₁) (k₂′<b₂ ∷ σ₂) (Succ ∈₁) (x₁ ∷ ∉₂) with k₁′ ⋚ k₂′ | k₁′ ⋚ᴾ k₂′ | k₁′ ⋚ᴸ k₂′
  … | [<] | [<] k′<k | [<] = Succ (↦∈[⧺]/L k v f kvs₁ (⟨ k₂′ , v₂′ ⟩ ∷ kvs₂) σ₁ (k₂′<b₂ ∷ σ₂) ∈₁ (x₁ ∷ ∉₂))
  … | [≡] | [≡] k′≡k | [≡] rewrite k′≡k = Succ (↦∈[⧺]/L k v f kvs₁ kvs₂ σ₁ σ₂ ∈₁ ∉₂)
  … | [>] | [>] k′>k | [>] = Succ (↦∈[⧺]/L k v f (⟨ k₁′ , v₁′ ⟩ ∷ kvs₁) kvs₂ (k₁′<b₁ ∷ σ₁) σ₂ (Succ ∈₁) ∉₂)
  
  _[_]ᴾ‖_ : ∀ {b} kvs k → sorted b kvs → k ↦∈!ᴾ kvs
  [] [ k ]ᴾ‖ _ = ✗ []
  (⟨ k′ , v′ ⟩ ∷ kvs) [ k ]ᴾ‖ (k′<b ∷ σ) with k ⋚ᴾ k′
  … | [<] k<k′ = ✗ (strict[<]/≡[ K ] k<k′ ∷ (k <[ kvs ]‖[ k′<b ⊚ ⟨ k<k′ ⟩ , σ ] ))
  … | [≡] k≡k′ rewrite k≡k′ = ✓ Zero
  … | [>] k>k′ with kvs [ k ]ᴾ‖ σ
  … | ✓ k∈kvs = ✓ (Succ k∈kvs)
  … | ✗ k∉kvs = ✗ ((λ k≡k′ → strict[<]/≡[ K ] k>k′ (◇ k≡k′)) ∷ k∉kvs)

  _[_]ᴸ‖_ : ∀ {b} kvs k (σ : sorted b kvs) → k ↦∈!ᴸ kvs ‖[ kvs [ k ] ,  kvs [ k ]ᴾ‖ σ ]
  [] [ k ]ᴸ‖ σ = ✗
  (⟨ k′ , v′ ⟩ ∷ kvs) [ k ]ᴸ‖ (k′<b ∷ σ) with k ⋚ k′ | k ⋚ᴾ k′ | k ⋚ᴸ k′
  … | [<] | [<] k<k′ | [<] = ✗
  … | [≡] | [≡] k≡k′ | [≡] rewrite k≡k′ = ✓
  … | [>] | [>] k>k′ | [>] with kvs [ k ] | kvs [ k ]ᴾ‖ σ | kvs [ k ]ᴸ‖ σ
  … | None | ✗ k∉kvs | ✗ = ✗
  … | Some v | ✓ k∈kvs | ✓ = ✓

  _∈?ᴾ_‖_ : ∀ {b} k kvs → sorted b kvs → k ∈!ᴾ kvs
  k ∈?ᴾ [] ‖ σ = ✗ []
  k ∈?ᴾ ⟨ k′ , v′ ⟩ ∷ kvs ‖ (k′<b ∷ σ) with k ⋚ᴾ k′
  … | [<] k<k′ = ✗ ((strict[<]/≡[ K ] k<k′) ∷ (k <[ kvs ]‖[ k′<b ⊚ ⟨ k<k′ ⟩ , σ ]))
  … | [≡] k≡k′ rewrite k≡k′ = ✓ Zero
  … | [>] k>k′ with k ∈?ᴾ kvs ‖ σ
  … | ✓ k∈kvs = ✓ (Succ k∈kvs)
  … | ✗ k∉kvs = ✗ ((λ k≡k′ → strict[<]/≡[ K ] k>k′ (◇ k≡k′)) ∷ k∉kvs)

  _∈?ᴸ_‖_ : ∀ {b} k kvs (σ : sorted b kvs) → k ∈!ᴸ kvs ‖[ k ∈? kvs , k ∈?ᴾ kvs ‖ σ ]
  k ∈?ᴸ [] ‖ σ = ✗
  k ∈?ᴸ ⟨ k′ , v′ ⟩ ∷ kvs ‖ (k′<b ∷ σ) with k ⋚ k′ | k ⋚ᴾ k′ | k ⋚ᴸ k′
  … | [<] | [<] k<k′ | [<] = ✗
  … | [≡] | [≡] k≡k′ | [≡] rewrite k≡k′ = ✓
  … | [>] | [>] k>k′ | [>] with k ∈? kvs | k ∈?ᴾ kvs ‖ σ | k ∈?ᴸ kvs ‖ σ
  … | ✗ | ✗ k∉kvs | ✗ = ✗
  … | ✓ | ✓ k∈kvs | ✓ = ✓

syntax ⇰[] K V b = K ⇰[ b ] V
⇰[] : ∀ {ℓ ℓʳ} (K : Set ℓ) {{_ : Order ℓʳ K}} (V : Set ℓ) → add-⊤ K → Set (ℓ ⊔ᴸ ℓʳ)
K ⇰[ b ] V = ∃ᴵ xs ⦂ list (K ∧ V) 𝑠𝑡 sorted b xs

data _⇰_ {ℓ ℓʳ} (K : Set ℓ) {{_ : Order ℓʳ K}} (V : Set ℓ) : Set (ℓ ⊔ᴸ ℓʳ) where
  ⟨_⟩ : ∀ {b} → K ⇰[ b ] V → K ⇰ V

-- data ⇰[] {ℓ ℓʳ} (A : Set ℓ) {{_ : Order ℓʳ A}} (B : Set ℓ) : add-⊤ A → Set (ℓ ⊔ᴸ ℓʳ) where
--   [] : A ⇰[ ⊤ ] B
--   _⋄_⋄_∷_ : ∀ {b} (x : A) → B → ⟨ x ⟩ < b → A ⇰[ b ] B → A ⇰[ ⟨ x ⟩ ] B

-- data _⇰_ {ℓ ℓʳ} (A : Set ℓ) {{_ : Order ℓʳ A}} (B : Set ℓ) : Set (ℓ ⊔ᴸ ℓʳ) where
--   FM : ∀ {b} → A ⇰[ b ] B → A ⇰ B
-- 
-- module _ {ℓ ℓʳ} {A : Set ℓ} {{_ : Order ℓʳ A}} {B : Set ℓ} where
--   infixr 22 ⩌ᵇ[]
--   infixr 22 ⩌[]
--   infix 14 ⟨_↦_⟩∈ᵇ_
--   infix 14 ⟨_↦_⟩∈_
--   infix 14 _↦∈ᵇ_
--   infix 14 _↦∈_
--   infix 14 _↦∉ᵇ_
--   infix 14 _↦∉_
-- 
--   syntax ⩌ᵇ[] f xs ys = xs ⩌ᵇ[ f ] ys
--   ⩌ᵇ[] : ∀ {b₁ b₂} → (B → B → B) → A ⇰[ b₁ ] B → A ⇰[ b₂ ] B → A ⇰[ b₁ ⩓ b₂ ] B
--   ⩌ᵇ[] {.⊤} {b₂} f [] ys rewrite left-unit[⊤]/≤[ b₂ ] = ys
--   ⩌ᵇ[] {b₁} {.⊤} f xs [] rewrite right-unit[⊤]/≤[ b₁ ] = xs
--   ⩌ᵇ[] f (x₁ ⋄ y₁ ⋄ <₁ ∷ xs₁) (x₂ ⋄ y₂ ⋄ <₂ ∷ xs₂) with x₁ ⋚ᴾ x₂
--   … | [<] x₁<x₂ = {!!} -- x₁ ⋄ y₁ ⋄ tight[⩓]/<[ add-⊤ A ] <₁ ⟨ x₁<x₂ ⟩ ∷ (xs₁ ⩌ᵇ[ f ] x₂ ⋄ y₂ ⋄ <₂ ∷ xs₂)
--   … | [≡] x₁≡x₂ rewrite x₁≡x₂ = {!!} -- x₂ ⋄ f y₁ y₂ ⋄ tight[⩓]/<[ add-⊤ A ] <₁ <₂ ∷ (xs₁ ⩌ᵇ[ f ] xs₂)
--   … | [>] x₁>x₂ = {!!} -- x₂ ⋄ y₂ ⋄ tight[⩓]/<[ add-⊤ A ] ⟨ x₁>x₂ ⟩ <₂ ∷ (x₁ ⋄ y₁ ⋄ <₁ ∷ xs₁ ⩌ᵇ[ f ] xs₂)
-- 
--   _[_]ᵇ : ∀ {b} → A ⇰[ b ] B → A → option B
--   [] [ x ]ᵇ = None
--   (x′ ⋄ y′ ⋄ <ˣ ∷ xs) [ x ]ᵇ = {!!}
-- 
--   data ⟨_↦_⟩∈ᵇ_ : ∀ {b} → A → B → A ⇰[ b ] B → Set (ℓ ⊔ᴸ ℓʳ) where
--     Zero : ∀ {x y b <ˣ} {xs : A ⇰[ b ] B}
--       → ⟨ x ↦ y ⟩∈ᵇ x ⋄ y ⋄ <ˣ ∷ xs
--     Succ : ∀ {x y x′ y′ b <ˣ} {xs : A ⇰[ b ] B}
--       → ⟨ x ↦ y ⟩∈ᵇ xs
--       → ⟨ x ↦ y ⟩∈ᵇ x′ ⋄ y′ ⋄ <ˣ ∷ xs
--   
--   data _↦∈ᵇ_ : ∀ {b} → A → A ⇰[ b ] B → Set (ℓ ⊔ᴸ ℓʳ) where
--     Zero : ∀ {x y b <ˣ} {xs : A ⇰[ b ] B}
--       → x ↦∈ᵇ x ⋄ y ⋄ <ˣ ∷ xs
--     Succ : ∀ {x x′ y′ b <ˣ} {xs : A ⇰[ b ] B}
--       → x ↦∈ᵇ xs
--       → x ↦∈ᵇ x′ ⋄ y′ ⋄ <ˣ ∷ xs
-- 
--   data _↦∉ᵇ_ : ∀ {b} → A → A ⇰[ b ] B → Set (ℓ ⊔ᴸ ℓʳ) where
--     Zero : ∀ {x}
--       → x ↦∉ᵇ []
--     Succ : ∀ {x x′ y′ b <ˣ} {xs : A ⇰[ b ] B}
--       → x ≢ x′
--       → x ↦∉ᵇ xs
--       → x ↦∉ᵇ (x′ ⋄ y′ ⋄ <ˣ ∷ xs)
-- 
--   dec[∈]⸢fmap′/>⸣ : ∀ {b} x (xs : A ⇰[ b ] B) → ⟨ x ⟩ < b → x ↦∉ᵇ xs
--   dec[∈]⸢fmap′/>⸣ x [] >ˣ = Zero
--   dec[∈]⸢fmap′/>⸣ x (x′ ⋄ y′ ⋄ <ˣ ∷ xs) >ˣ = Succ (λ x≡x′ → strict[<][ add-⊤ A ] >ˣ ⟨ xRx[≡][≤] (◇ x≡x′) ⟩) (dec[∈]⸢fmap′/>⸣ x xs (<ˣ ⊚ >ˣ))
-- 
--   dec[∈]⸢fmap′/≤⸣ : ∀ {b} x (xs : A ⇰[ b ] B) → (∃ y 𝑠𝑡 ⟨ x ↦ y ⟩∈ᵇ xs) ∨ x ↦∉ᵇ xs
--   dec[∈]⸢fmap′/≤⸣ x [] = Inr Zero
--   dec[∈]⸢fmap′/≤⸣ x (_⋄_⋄_∷_ {b} x′ y′ <ˣ xs) with x ⋚ᴾ x′
--   … | [<] x<x′ = Inr (dec[∈]⸢fmap′/>⸣ x (x′ ⋄ y′ ⋄ <ˣ ∷ xs) ⟨ x<x′ ⟩)
--   … | [≡] x≡x′ rewrite x≡x′ = Inl ∃⟨ y′ , Zero ⟩
--   … | [>] x>x′ with ⟨ x ⟩ ⋚ᴾ b
--   dec[∈]⸢fmap′/≤⸣ x (x′ ⋄ y′ ⋄ <ˣ ∷ xs) | [>] x>x′ | [<] x<b = Inr (Succ (λ x≡x′ → strict[<][ A ] x>x′ (xRx[≡][≤] x≡x′)) (dec[∈]⸢fmap′/>⸣ x xs x<b))
--   dec[∈]⸢fmap′/≤⸣ x (x′ ⋄ y′ ⋄ <ˣ₁ ∷ (.x ⋄ y′′ ⋄ <ˣ₂ ∷ xs)) | [>] x>x′ | [≡] ↯ = Inl ∃⟨ y′′ , Succ Zero ⟩
--   dec[∈]⸢fmap′/≤⸣ x (x′ ⋄ y′ ⋄ <ˣ ∷ xs) | [>] x>x′ | [>] x>b with dec[∈]⸢fmap′/≤⸣ x xs
--   … | Inl ∃⟨ y , ∈ʸ ⟩ = Inl ∃⟨ y , Succ ∈ʸ ⟩
--   … | Inr ∉ˣ = Inr (Succ (λ x≡x′ → strict[<][ add-⊤ A ] (x>b ⊚ <ˣ) ⟨ xRx[≡][≤] x≡x′ ⟩) ∉ˣ)
-- 
-- 
--   syntax ⩌[] f xs ys = xs ⩌[ f ] ys
--   ⩌[] : (B → B → B) → A ⇰ B → A ⇰ B → A ⇰ B
--   ⩌[] f (FM xs) (FM ys) = FM (xs ⩌ᵇ[ f ] ys)
-- 
--   data ⟨_↦_⟩∈_ : A → B → A ⇰ B → Set (ℓ ⊔ᴸ ℓʳ) where
--     FM : ∀ {x y b} {xs : A ⇰[ b ] B}
--       → ⟨ x ↦ y ⟩∈ᵇ xs
--       → ⟨ x ↦ y ⟩∈ FM xs
-- 
--   data _↦∈_ : A → A ⇰ B → Set (ℓ ⊔ᴸ ℓʳ) where
--     FM : ∀ {x b} {xs : A ⇰[ b ] B}
--       → x ↦∈ᵇ xs
--       → x ↦∈ FM xs
-- 
--   data _↦∉_ : A → A ⇰ B → Set (ℓ ⊔ᴸ ℓʳ) where
--     FM : ∀ {x b} {xs : A ⇰[ b ] B}
--       → x ↦∉ᵇ xs
--       → x ↦∉ FM xs
--   
--   data _⫑ᵇ_ : ∀ {b₁ b₂} → A ⇰[ b₁ ] B → A ⇰[ b₂ ] B → Set (ℓ ⊔ᴸ ℓʳ) where
--     [] : ∀ {b} {xs : A ⇰[ b ] B} → [] ⫑ᵇ xs
--     Hit : ∀ {x y b₁ <ˣ₁ b₂ <ˣ₂} {xs₁ : A ⇰[ b₁ ] B} {xs₂ : A ⇰[ b₂ ] B}
--       → xs₁ ⫑ᵇ xs₂
--       → (x ⋄ y ⋄ <ˣ₁ ∷ xs₁) ⫑ᵇ (x ⋄ y ⋄ <ˣ₂ ∷ xs₂)
--     Miss : ∀ {x₁ y₁ b₁ <ˣ₁ x₂ y₂ b₂ <ˣ₂} {xs₁ : A ⇰[ b₁ ] B} {xs₂ : A ⇰[ b₂ ] B}
--       → (x₁ ⋄ y₁ ⋄ <ˣ₁ ∷ xs₁) ⫑ᵇ xs₂
--       → (x₁ ⋄ y₁ ⋄ <ˣ₁ ∷ xs₁) ⫑ᵇ (x₂ ⋄ y₂ ⋄ <ˣ₂ ∷ xs₂)
-- 
--   data _⫑⸢fmap⸣_ : A ⇰ B → A ⇰ B → Set (ℓ ⊔ᴸ ℓʳ) where
--     FM : ∀ {b₁ b₂} {xs₁ : A ⇰[ b₁ ] B} {xs₂ : A ⇰[ b₂ ] B}
--       → xs₁ ⫑ᵇ xs₂
--       → FM xs₁ ⫑⸢fmap⸣ FM xs₂
-- 
--   ∅⸢⇰⸣ : A ⇰ B
--   ∅⸢⇰⸣ = FM []
--   postulate
--     sound[⫑]ᵇ : ∀ {x b₁ b₂} {xs₁ : A ⇰[ b₁ ] B} {xs₂ : A ⇰[ b₂ ] B} → xs₁ ⫑ᵇ xs₂ → x ↦∈ᵇ xs₁ → x ↦∈ᵇ xs₂
--     complete[⫑]ᵇ : ∀ {b₁ b₂} {xs₁ : A ⇰[ b₁ ] B} {xs₂ : A ⇰[ b₂ ] B} → (∀ {x} → x ↦∈ᵇ xs₁ → x ↦∈ᵇ xs₂) → xs₁ ⫑ᵇ xs₂
--     _[_] : A ⇰ B → A → option B
--     -- _[_]! : ∀ (xs : A ⇰ B) (x : A) → (x ∉ xs) ∨ (∃ v 𝑠𝑡 ⟨ x ↦ v ⟩∈ xs)
--     unique/∈ : ∀ {xs : A ⇰ B} {x : A} {y : B} → ⟨ x ↦ y ⟩∈ xs → xs [ x ] ≡ Some y
--     unique/∉ : ∀ {xs : A ⇰ B} {x : A} → x ↦∉ xs → xs [ x ] ≡ None
--     _[_‖_]⸢⇰⸣ : ∀ (xs : A ⇰ B) (x : A) → x ↦∈ xs → B
--     _[_↦_]⸢⇰⸣ : A ⇰ B → A → B → A ⇰ B
-- 
--   -- LOH: defein ⟨x x ⟩∈ᵇ[ xs ], give it a better name, and complete sound/complete
