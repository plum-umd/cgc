module AGT.SimplyTyped.Abstract where

open import Prelude
open import POSet

open import AGT.SimplyTyped.Concrete

infix   3 _~_
infixr  4 _⟨→⟩_
infix   8 _∈♯_
infix   8 _⊢♯_
infix   8 _⊴ᵗ♯_
infixr  9 _⌾⸢⊴ᵗ♯⸣_
infixr 10 _∷_

-------------
-- [type♯] --
-------------

data type♯ : Set where
  ⊥ : type♯
  ⊤ : type♯
  ⟨𝔹⟩ : type♯
  _⟨→⟩_ : type♯ → type♯ → type♯

----------------------
-- order on [type♯] --
----------------------

data _⊴ᵗ♯_ : relation zeroˡ type♯ where
  ⊥ : ∀ {τ} → ⊥ ⊴ᵗ♯ τ
  ⊤ : ∀ {τ} → τ ⊴ᵗ♯ ⊤
  ⟨𝔹⟩ : ⟨𝔹⟩ ⊴ᵗ♯ ⟨𝔹⟩
  _⟨→⟩_ : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂}
    → τ₁₁ ⊴ᵗ♯ τ₂₁
    → τ₁₂ ⊴ᵗ♯ τ₂₂
    → (τ₁₁ ⟨→⟩ τ₁₂) ⊴ᵗ♯ (τ₂₁ ⟨→⟩ τ₂₂)

xRx⸢⊴ᵗ♯⸣ : reflexive _⊴ᵗ♯_
xRx⸢⊴ᵗ♯⸣ {⊥} = ⊥
xRx⸢⊴ᵗ♯⸣ {⊤} = ⊤
xRx⸢⊴ᵗ♯⸣ {⟨𝔹⟩} = ⟨𝔹⟩
xRx⸢⊴ᵗ♯⸣ {τ₁ ⟨→⟩ τ₂} = xRx⸢⊴ᵗ♯⸣ ⟨→⟩ xRx⸢⊴ᵗ♯⸣

_⌾⸢⊴ᵗ♯⸣_ : transitive _⊴ᵗ♯_
_ ⌾⸢⊴ᵗ♯⸣ ⊥ = ⊥
⊤ ⌾⸢⊴ᵗ♯⸣ _ = ⊤
⟨𝔹⟩ ⌾⸢⊴ᵗ♯⸣ ⟨𝔹⟩ = ⟨𝔹⟩
(y₁⊴z₁ ⟨→⟩ y₂⊴z₂) ⌾⸢⊴ᵗ♯⸣ (x₁⊴y₁ ⟨→⟩ x₂⊴y₂) = y₁⊴z₁ ⌾⸢⊴ᵗ♯⸣ x₁⊴y₁ ⟨→⟩ y₂⊴z₂ ⌾⸢⊴ᵗ♯⸣ x₂⊴y₂

instance
  Reflexive[⊴ᵗ♯] : Reflexive _⊴ᵗ♯_
  Reflexive[⊴ᵗ♯] = record { xRx = xRx⸢⊴ᵗ♯⸣ }
  Transitive[⊴ᵗ♯] : Transitive _⊴ᵗ♯_
  Transitive[⊴ᵗ♯] = record { _⌾_ = _⌾⸢⊴ᵗ♯⸣_ }
  PreOrder[type♯] : PreOrder zeroˡ type♯
  PreOrder[type♯] = record { _⊴_ = _⊴ᵗ♯_ }

---------------------
-- [type ⇄ᶜ type♯] --
---------------------

data _∈γ[_] : type → type♯ → Set where
  ⊥ : ∀ {τ♯} → ⊥ ∈γ[ τ♯ ]
  ⊤ : ∀ {τ} → τ ∈γ[ ⊤ ]
  ⟨𝔹⟩ : ⟨𝔹⟩ ∈γ[ ⟨𝔹⟩ ]
  _⟨→⟩_ : ∀ {τ₁ τ₂ τ₁♯ τ₂♯}
    → τ₁ ∈γ[ τ₁♯ ]
    → τ₂ ∈γ[ τ₂♯ ]
    → (τ₁ ⟨→⟩ τ₂) ∈γ[ τ₁♯ ⟨→⟩ τ₂♯ ]

γ : type♯ → type → Set
γ τ♯ τ = τ ∈γ[ τ♯ ]

monotonic[γ] : proper (_⊴_ ⇉ _⊵_ ⇉ [→]) γ
monotonic[γ] _ ⊥ ⊥ = ⊥
monotonic[γ] ⊤ _ ⊤ = ⊤
monotonic[γ] ⟨𝔹⟩ ⟨𝔹⟩ ⟨𝔹⟩ = ⟨𝔹⟩
monotonic[γ] (⊴₁₁ ⟨→⟩ ⊴₂₁) (⊴₁₂ ⟨→⟩ ⊴₂₂) (∈γ₁ ⟨→⟩ ∈γ₂) = monotonic[γ] ⊴₁₁ ⊴₁₂ ∈γ₁ ⟨→⟩ monotonic[γ] ⊴₂₁ ⊴₂₂ ∈γ₂
monotonic[γ] _ ⊥ _ = ⊥
monotonic[γ] ⊤ _ _ = ⊤

η : type → type♯
η ⊥ = ⊥
η ⟨𝔹⟩ = ⟨𝔹⟩
η (τ₁ ⟨→⟩ τ₂) = η τ₁ ⟨→⟩ η τ₂

monotonic[η] : proper (_⊴_ ⇉ _⊴_) η
monotonic[η] ⊥ = ⊥
monotonic[η] ⟨𝔹⟩ = ⟨𝔹⟩
monotonic[η] (τ₁ ⟨→⟩ τ₂) = monotonic[η] τ₁ ⟨→⟩ monotonic[η] τ₂

sound[ηγ] : ∀ {τ} → τ ∈γ[ η τ ]
sound[ηγ] {⊥} = ⊥
sound[ηγ] {⟨𝔹⟩} = ⟨𝔹⟩
sound[ηγ] {τ ⟨→⟩ τ₁} = sound[ηγ] ⟨→⟩ sound[ηγ]

complete[ηγ] : ∀ {τ τ♯} → τ ∈γ[ τ♯ ] → η τ ⊴ᵗ♯ τ♯
complete[ηγ] ⊥ = ⊥
complete[ηγ] ⊤ = ⊤
complete[ηγ] ⟨𝔹⟩ = ⟨𝔹⟩
complete[ηγ] (τ₁∈γ[τ₁♯] ⟨→⟩ τ₂∈γ[τ₂♯]) = complete[ηγ] τ₁∈γ[τ₁♯] ⟨→⟩ complete[ηγ] τ₂∈γ[τ₂♯]

-- (Proposition 3 and 4)

⇄type⇄ : ⇧ type ⇄ᶜ ⇧ type♯
⇄type⇄ = mk[⇄ᶜ]⸢↑⸣ record
  { η = η
  ; monotonic[η] = monotonic[η]
  ; γ = γ
  ; monotonic[γ] = monotonic[γ]
  ; sound = sound[ηγ]
  ; complete = complete[ηγ]
  }

injective[γ] : ∀ τ₁♯ τ₂♯ → (∀ τ → τ ∈γ[ τ₁♯ ] → τ ∈γ[ τ₂♯ ]) → τ₁♯ ⊴ τ₂♯
injective[γ] ⟨𝔹⟩ ⟨𝔹⟩ _ = ⟨𝔹⟩
injective[γ] (τ₁₁♯ ⟨→⟩ τ₂₁♯) (τ₁₂♯ ⟨→⟩ τ₂₂♯) ⊆₁ = injective[γ] τ₁₁♯ τ₁₂♯ F₁ ⟨→⟩ injective[γ] τ₂₁♯ τ₂₂♯ F₂
  where
    F₁ : ∀ τ → τ ∈γ[ τ₁₁♯ ] → τ ∈γ[ τ₁₂♯ ]
    F₁ τ₁ τ₁∈γ[τ₁₁♯] with ⊆₁ (τ₁ ⟨→⟩ ⊥) (τ₁∈γ[τ₁₁♯] ⟨→⟩ ⊥)
    ... | ∈γ₁ ⟨→⟩ ∈γ₂ = ∈γ₁
    F₂ : ∀ τ → τ ∈γ[ τ₂₁♯ ] → τ ∈γ[ τ₂₂♯ ]
    F₂ τ₂ τ₂∈γ[τ₂₁♯] with ⊆₁ (⊥ ⟨→⟩ τ₂) (⊥ ⟨→⟩ τ₂∈γ[τ₂₁♯])
    ... | ∈γ₁ ⟨→⟩ ∈γ₂ = ∈γ₂
injective[γ] ⟨𝔹⟩ (_ ⟨→⟩ _) ⊆₁ = case ⊆₁ ⟨𝔹⟩ ⟨𝔹⟩ 𝑜𝑓 λ ()
injective[γ] (τ₁♯ ⟨→⟩ τ₂♯) ⟨𝔹⟩ ⊆₁ = case ⊆₁ (⊥ ⟨→⟩ ⊥) (⊥ ⟨→⟩ ⊥) 𝑜𝑓 λ ()
injective[γ] ⊤ ⟨𝔹⟩ ⊆₁ = case ⊆₁ (⟨𝔹⟩ ⟨→⟩ ⟨𝔹⟩) ⊤ 𝑜𝑓 λ ()
injective[γ] ⟨𝔹⟩ ⊥ ⊆₁ = case ⊆₁ ⟨𝔹⟩ ⟨𝔹⟩ 𝑜𝑓 λ ()
injective[γ] (τ₁♯ ⟨→⟩ τ₂♯) ⊥ ⊆₁ = case ⊆₁ (⊥ ⟨→⟩ ⊥) (⊥ ⟨→⟩ ⊥) 𝑜𝑓 λ ()
injective[γ] ⊤ (τ₁ ⟨→⟩ τ₂) ⊆₁ = case ⊆₁ ⟨𝔹⟩ ⊤ 𝑜𝑓 λ ()
injective[γ] ⊤ ⊥ ⊆₁ = case ⊆₁ ⟨𝔹⟩ ⊤ 𝑜𝑓 λ ()
injective[γ] ⊥ _ _ = ⊥
injective[γ] _ ⊤ _ = ⊤

-- (Proposition 1)

prop₁ : ∀ τ₁♯ τ₂♯ → γᶜ[ ⇄type⇄ ] ⋅ ↑ τ₁♯ ⊑ γᶜ[ ⇄type⇄ ] ⋅ ↑ τ₂♯ ↔ ↑ τ₁♯ ⊑ ↑ τ₂♯
prop₁ τ₁♯ τ₂♯ = LHS τ₁♯ τ₂♯ , RHS τ₁♯ τ₂♯
  where
    LHS : ∀ τ₁♯ τ₂♯ → γᶜ[ ⇄type⇄ ] ⋅ ↑ τ₁♯ ⊑ γᶜ[ ⇄type⇄ ] ⋅ ↑ τ₂♯ → ↑ τ₁♯ ⊑ ↑ τ₂♯
    LHS τ₁♯ τ₂♯ ↑⟨ ↑⟨ ⊆₁ ⟩ ⟩ = ↑⟨ (injective[γ] τ₁♯ τ₂♯ (λ τ ∈γ → ⊆₁ {x = ↑⟨ τ ⟩} {y = ↑⟨ τ ⟩} xRx ∈γ )) ⟩
    RHS : ∀ τ₁♯ τ₂♯ → ↑ τ₁♯ ⊑ ↑ τ₂♯ → γᶜ[ ⇄type⇄ ] ⋅ ↑ τ₁♯ ⊑ γᶜ[ ⇄type⇄ ] ⋅ ↑ τ₂♯
    RHS τ₁♯ τ₂♯ τ₁♯⊑τ₂♯ = res-x[⇒]⸢⊑⸣ {f = γᶜ[ ⇄type⇄ ]} τ₁♯⊑τ₂♯

--------------
-- [lift-P] --
--------------

data is[⊥] : type → Set where
  ⊥ : is[⊥] ⊥
  ⊥⟨→⟩ : ∀ {τ₁ τ₂} → is[⊥] τ₁ → is[⊥] (τ₁ ⟨→⟩ τ₂)
  ⟨→⟩⊥ : ∀ {τ₁ τ₂} → is[⊥] τ₂ → is[⊥] (τ₁ ⟨→⟩ τ₂)

data is♯[⊥] : type♯ → Set where
  ⊥ : is♯[⊥] ⊥
  ⊥⟨→⟩ : ∀ {τ₁ τ₂} → is♯[⊥] τ₁ → is♯[⊥] (τ₁ ⟨→⟩ τ₂)
  ⟨→⟩⊥ : ∀ {τ₁ τ₂} → is♯[⊥] τ₂ → is♯[⊥] (τ₁ ⟨→⟩ τ₂)

data lift-P (p : type → type → Set) (τ₁♯ : type♯) (τ₂♯ : type♯) : Set where
  Lift-P : ∀ {τ₁ τ₂} → not (is[⊥] τ₁) → not (is[⊥] τ₂) → τ₁ ∈γ[ τ₁♯ ] → τ₂ ∈γ[ τ₂♯ ] → p τ₁ τ₂ → lift-P p τ₁♯ τ₂♯

-- module _ (NOT-TRUE : void) where
--   monotonic[lift-P] : proper ((_⊴_ ⇉ _⊵_ ⇉ [→]) ⇉ _⊴_ ⇉ _⊵_ ⇉ [→]) lift-P
--   monotonic[lift-P] {p₁} {p₂} p₁⊑p₂ {τ₁₁♯} {τ₁₂♯} τ₁₁♯⊴τ₁₂♯ {τ₂₁♯} {τ₂₂♯} τ₂₂♯⊴τ₂₁ (Lift-P {τ₁} {τ₂} τ₁∈γ[τ₁₁♯] τ₂∈γ[τ₂₁♯] p₁[τ₁,τ₂]) =
--     Lift-P {p₂} {τ₁₂♯} {τ₂₂♯} {τ₁} {τ₂} (monotonic[γ] τ₁₁♯⊴τ₁₂♯ xRx τ₁∈γ[τ₁₁♯]) (exfalso NOT-TRUE) (p₁⊑p₂ xRx xRx p₁[τ₁,τ₂])
-- 
--   lift-P⁺ : ⟪ (⇧ type ⇒ 𝒫 (⇧ type)) ⇒ (⇧ type♯ ⇒ 𝒫 (⇧ type♯)) ⟫
--   lift-P⁺ = witness-x (curry⸢λ⸣ $ curry⸢λ↑⸣ id⸢ω↑⸣) $ mk[witness] (λ p → lift-P (λ τ₁ τ₂ → ↑⟨ τ₂ ⟩ ⋿ p ⋅ ↑⟨ τ₁ ⟩)) ppr
--     where
--       ppr : proper (_⊑_ ⇉ _⊴_ ⇉ _⊵_ ⇉ [→]) (λ p → lift-P (λ τ₁ τ₂ → ↑⟨ τ₂ ⟩ ⋿ p ⋅ ↑⟨ τ₁ ⟩))
--       ppr {p₁} {p₂} p₁⊑p₂ {τ₁₁♯} {τ₁₂♯} τ₁₁♯⊴τ₁₂♯ {τ₂₁♯} {τ₂₂♯} τ₂₂♯⊴τ₂₁ lift-P[…] =
--         monotonic[lift-P] (λ τ₁₁⊴τ₂₁ τ₁₂⊴τ₂₂ τ₂₂∈p[τ₁₁] → res-X-x[𝒫]⸢⊑⸣ (res-f-x[⇒]⸢⊑⸣ p₁⊑p₂ ↑⟨ τ₁₁⊴τ₂₁ ⟩) ↑⟨ τ₁₂⊴τ₂₂ ⟩ τ₂₂∈p[τ₁₁]) τ₁₁♯⊴τ₁₂♯ τ₂₂♯⊴τ₂₁ lift-P[…]

-----------
-- [_~_] --
-----------

data _~_ : type♯ → type♯ → Set where
  τR⊤ : ∀ {τ} → τ ~ ⊤
  ⊤Rτ : ∀ {τ} → ⊤ ~ τ
  ⟨𝔹⟩ : ⟨𝔹⟩ ~ ⟨𝔹⟩
  _⟨→⟩_ : ∀ {τ₁₁ τ₂₁ τ₁₂ τ₂₂}
    → τ₁₁ ~ τ₂₁
    → τ₁₂ ~ τ₂₂
    → τ₁₁ ⟨→⟩ τ₁₂ ~ τ₂₁ ⟨→⟩ τ₂₂

-- (Proposition 2)

∃∈γ : ∀ τ♯ → not (is♯[⊥] τ♯) → ∃ τ 𝑠𝑡 τ ∈γ[ τ♯ ] × not (is[⊥] τ)
∃∈γ ⊥ not[⊥] = exfalso (not[⊥] ⊥)
∃∈γ ⊤ _ = ∃ ⟨𝔹⟩ ,, ⊤ , λ ()
∃∈γ ⟨𝔹⟩ _ = ∃ ⟨𝔹⟩ ,, ⟨𝔹⟩ , λ ()
∃∈γ (τ₁♯ ⟨→⟩ τ₂♯) not[⊥] with ∃∈γ τ₁♯ (λ is[⊥]' → not[⊥] (⊥⟨→⟩ is[⊥]')) | ∃∈γ τ₂♯ (λ is[⊥]' → not[⊥] (⟨→⟩⊥ is[⊥]'))
... | ∃ τ₁ ,, τ₁∈γ[τ₁♯] , not[⊥]₁ | ∃ τ₂ ,, τ₂∈γ[τ₂♯] , not[⊥]₂ =
  ∃ τ₁ ⟨→⟩ τ₂
  ,, (τ₁∈γ[τ₁♯] ⟨→⟩ τ₂∈γ[τ₂♯])
  , (λ{ (⟨→⟩⊥ is[⊥]') → not[⊥]₂ is[⊥]' ; (⊥⟨→⟩ is[⊥]') → not[⊥]₁ is[⊥]'})

prop₂ : ∀ τ₁♯ τ₂♯ → not (is♯[⊥] τ₁♯) → not (is♯[⊥] τ₂♯) → lift-P _≡_ τ₁♯ τ₂♯ ↔ (τ₁♯ ~ τ₂♯)
prop₂ τ₁♯ τ₂♯ not[⊥]₁ not[⊥]₂ = LHS τ₁♯ τ₂♯ , RHS τ₁♯ τ₂♯ not[⊥]₁ not[⊥]₂
  where
    LHS : ∀ τ₁♯ τ₂♯ → lift-P _≡_ τ₁♯ τ₂♯ → τ₁♯ ~ τ₂♯
    LHS τ₁♯ τ₂♯ (Lift-P τ₁≢⊥ τ₂≢⊥ τ₁∈γ[τ₁♯] τ₂∈γ[τ₂♯] ↯) = consistent τ₁≢⊥ τ₁∈γ[τ₁♯] τ₂∈γ[τ₂♯]
      where
        consistent : ∀ {τ τ₁♯ τ₂♯} → not (is[⊥] τ) → τ ∈γ[ τ₁♯ ] → τ ∈γ[ τ₂♯ ] → τ₁♯ ~ τ₂♯
        consistent τ≢⊥ ⊥ _ = exfalso (τ≢⊥ ⊥)
        consistent τ≢⊥ _ ⊥ = exfalso (τ≢⊥ ⊥)
        consistent _ ⊤ _ = ⊤Rτ
        consistent _ _ ⊤ = τR⊤
        consistent _ ⟨𝔹⟩ ⟨𝔹⟩ = ⟨𝔹⟩
        consistent τ≢⊥₁ (τ₁₁ ⟨→⟩ τ₂₁) (τ₁₂ ⟨→⟩ τ₂₂) = consistent (λ τ≢⊥₂ → τ≢⊥₁ (⊥⟨→⟩ τ≢⊥₂)) τ₁₁ τ₁₂ ⟨→⟩ consistent (λ τ≢⊥₂ → τ≢⊥₁ (⟨→⟩⊥ τ≢⊥₂)) τ₂₁ τ₂₂
    RHS : ∀ τ₁♯ τ₂♯ → not (is♯[⊥] τ₁♯) → not (is♯[⊥] τ₂♯) → τ₁♯ ~ τ₂♯ → lift-P _≡_ τ₁♯ τ₂♯
    RHS τ♯ .⊤ not[⊥]₁ not[⊥]₂ τR⊤ with ∃∈γ τ♯ not[⊥]₁
    ... | ∃ τ ,, (τ∈γ[τ♯] , not[⊥][τ]) = Lift-P not[⊥][τ] not[⊥][τ] τ∈γ[τ♯] ⊤ ↯
    RHS .⊤ τ♯ not[⊥]₁ not[⊥]₂ ⊤Rτ with ∃∈γ τ♯ not[⊥]₂
    ... | ∃ τ ,, (τ∈γ[τ♯] , not[⊥][τ]) = Lift-P not[⊥][τ] not[⊥][τ] ⊤ τ∈γ[τ♯] ↯
    RHS .⟨𝔹⟩ .⟨𝔹⟩ not[⊥]₁ not[⊥]₂ ⟨𝔹⟩ = Lift-P (λ ()) (λ ()) ⟨𝔹⟩ ⟨𝔹⟩ ↯
    RHS (τ₁₁ ⟨→⟩ τ₂₁) (τ₁₂ ⟨→⟩ τ₂₂) not[⊥]₁ not[⊥]₂ (τ₁₁~τ₁₂ ⟨→⟩ τ₂₁~τ₂₂)
      with RHS τ₁₁ τ₁₂ (λ is[⊥]₁ → not[⊥]₁ (⊥⟨→⟩ is[⊥]₁)) (λ is[⊥]₁ → not[⊥]₂ (⊥⟨→⟩ is[⊥]₁)) τ₁₁~τ₁₂ 
         | RHS τ₂₁ τ₂₂ (λ is[⊥]₁ → not[⊥]₁ (⟨→⟩⊥ is[⊥]₁)) (λ is[⊥]₁ → not[⊥]₂ (⟨→⟩⊥ is[⊥]₁)) τ₂₁~τ₂₂ 
    ... | Lift-P not[⊥]₁₁ not[⊥]₂₁ τ₁∈γ[τ₁₁] τ₁∈γ[τ₁₂] ↯ | Lift-P not[⊥]₁₂ not[⊥]₂₂ τ₂∈γ[τ₂₁] τ₂∈γ[τ₂₂] ↯ =
      Lift-P
        (λ{ (⊥⟨→⟩ is[⊥]₁) → not[⊥]₂₁ is[⊥]₁ ; (⟨→⟩⊥ is[⊥]₁) → not[⊥]₂₂ is[⊥]₁ })
        (λ{ (⊥⟨→⟩ is[⊥]₁) → not[⊥]₂₁ is[⊥]₁ ; (⟨→⟩⊥ is[⊥]₁) → not[⊥]₂₂ is[⊥]₁ })
        (τ₁∈γ[τ₁₁] ⟨→⟩ τ₂∈γ[τ₂₁])
        (τ₁∈γ[τ₁₂] ⟨→⟩ τ₂∈γ[τ₂₂])
        ↯

----------------------------
-- [dom], [cod] and [_⊓_] --
----------------------------

dom♯ : type♯ → type♯
dom♯ ⊤ = ⊤
dom♯ (τ₁ ⟨→⟩ τ₂) = τ₁
dom♯ _ = ⊥

dom♯⁺ : ⟪ ⇧ type♯ ⇒ ⇧ type♯ ⟫
dom♯⁺ = witness-x (curry⸢λ↑⸣ id⸢λ↑⸣) $ mk[witness] dom♯ ppr
  where
    ppr : proper (_⊴_ ⇉ _⊴_) dom♯
    ppr {⊥} _ = ⊥
    ppr {_} {⊤} _ = ⊤
    ppr ⟨𝔹⟩ = ⊥
    ppr (x₁⊑y₁ ⟨→⟩ x₂⊑y₂) = x₁⊑y₁

-- (Proposition 5.1)

sound[dom] : ∀ {τ} → ηᶜ[ ⇄type⇄ ] ⋅ (dom⁺ ⋅ τ) ⊑ dom♯⁺ ⋅ (ηᶜ[ ⇄type⇄ ] ⋅ τ)
sound[dom] {↑⟨ ⊥ ⟩} = ↑⟨ ⊥ ⟩
sound[dom] {↑⟨ ⟨𝔹⟩ ⟩} = ↑⟨ ⊥ ⟩
sound[dom] {↑⟨ τ₁ ⟨→⟩ τ₂ ⟩} = ↑⟨ xRx ⟩

complete[dom] : ∀ {τ} → dom♯⁺ ⋅ (ηᶜ[ ⇄type⇄ ] ⋅ τ) ⊑ ηᶜ[ ⇄type⇄ ] ⋅ (dom⁺ ⋅ τ)
complete[dom] {↑⟨ ⊥ ⟩} = ↑⟨ ⊥ ⟩
complete[dom] {↑⟨ ⟨𝔹⟩ ⟩} = ↑⟨ ⊥ ⟩
complete[dom] {↑⟨ τ₁ ⟨→⟩ τ₂ ⟩} = ↑⟨ xRx ⟩

other[dom] : ∀ {τ} → dom♯⁺ ⋅ (ηᶜ[ ⇄type⇄ ] ⋅ τ) ≡ ηᶜ[ ⇄type⇄ ] ⋅ (dom⁺ ⋅ τ)
other[dom] {↑⟨ ⊥ ⟩} = ↯
other[dom] {↑⟨ ⟨𝔹⟩ ⟩} = ↯
other[dom] {↑⟨ τ₁ ⟨→⟩ τ₂ ⟩} = ↯

cod♯ : type♯ → type♯
cod♯ ⊤ = ⊤
cod♯ (τ₁ ⟨→⟩ τ₂) = τ₂
cod♯ _ = ⊥

cod♯⁺ : ⟪ ⇧ type♯ ⇒ ⇧ type♯ ⟫
cod♯⁺ = witness-x (curry⸢λ↑⸣ id⸢λ↑⸣) $ mk[witness] cod♯ ppr
  where
    ppr : proper (_⊴_ ⇉ _⊴_) cod♯
    ppr {⊥} _ = ⊥
    ppr {_} {⊤} _ = ⊤
    ppr ⟨𝔹⟩ = ⊥
    ppr (x₁⊑y₁ ⟨→⟩ x₂⊑y₂) = x₂⊑y₂

-- (Proposition 5.2)

sound[cod] : ∀ {τ} → ηᶜ[ ⇄type⇄ ] ⋅ (cod⁺ ⋅ τ) ⊑ cod♯⁺ ⋅ (ηᶜ[ ⇄type⇄ ] ⋅ τ)
sound[cod] {↑⟨ ⊥ ⟩} = ↑⟨ ⊥ ⟩
sound[cod] {↑⟨ ⟨𝔹⟩ ⟩} = ↑⟨ ⊥ ⟩
sound[cod] {↑⟨ τ₁ ⟨→⟩ τ₂ ⟩} = ↑⟨ xRx ⟩

pf : ∀ τ♯ → (pure ⋅ ηᶜ[ ⇄type⇄ ]) * ⋅ ((pure ⋅ cod⁺) * ⋅ (γᶜ[ ⇄type⇄ ] ⋅ τ♯)) ⊑ pure ⋅ cod♯⁺ ⋅ τ♯
pf τ♯₂ = ext[𝒫]⸢⊑⸣ (λ {τ♯₁} → ηγ τ♯₂ τ♯₁)
  where
    ηγ : ∀ τ♯₁ τ♯₂ → τ♯₂ ⋿ (pure ⋅ ηᶜ[ ⇄type⇄ ]) * ⋅ ((pure ⋅ cod⁺) * ⋅ (γᶜ[ ⇄type⇄ ] ⋅ τ♯₁)) → τ♯₂ ⋿ pure ⋅ cod♯⁺ ⋅ τ♯₁
    ηγ ↑⟨ τ♯₁ ⟩ ↑⟨ .⊥ ⟩ (∃𝒫 ↑⟨ .⊥ ⟩ ,, (∃𝒫 ↑⟨ .⊥ ⟩ ,, ⊥ ,, ↑⟨ ⊥ ⟩) ,, ↑⟨ ⊥ ⟩) = ↑⟨ ⊥ ⟩
    ηγ ↑⟨ .⊤ ⟩ ↑⟨ τ♯₂ ⟩ (∃𝒫 ↑⟨ τ₁ ⟩ ,, (∃𝒫 ↑⟨ τ₂ ⟩ ,, ⊤ ,, ↑⟨ τ₁⊑cod[τ₂] ⟩) ,, ↑⟨ τ♯₂⊑η[τ₁] ⟩) = ↑⟨ ⊤ ⟩
    ηγ ↑⟨ .⟨𝔹⟩ ⟩ ↑⟨ .⊥ ⟩ (∃𝒫 ↑⟨ .⊥ ⟩ ,, (∃𝒫 ↑⟨ .⟨𝔹⟩ ⟩ ,, ⟨𝔹⟩ ,, ↑⟨ ⊥ ⟩) ,, ↑⟨ ⊥ ⟩) = ↑⟨ ⊥ ⟩
    ηγ ↑⟨ τ♯₁₁ ⟨→⟩ τ♯₂₁ ⟩ ↑⟨ τ♯₂ ⟩ (∃𝒫 ↑⟨ τ₁ ⟩ ,, (∃𝒫 ↑⟨ τ₁₁ ⟨→⟩ τ₂₁ ⟩ ,, τ₁₁∈γ[τ♯₁₁] ⟨→⟩ τ₂₁∈γ[τ♯₂₁] ,, ↑⟨ τ₁⊑τ₂₁ ⟩) ,, ↑⟨ τ♯₂⊑η[τ₁] ⟩) =
      completeᶜ[ ⇄type⇄ ] {↑⟨ τ♯₂₁ ⟩} {↑⟨ τ₂₁ ⟩} τ₂₁∈γ[τ♯₂₁] ⌾ res-x[⇒]⸢⊑⸣ {f = ηᶜ[ ⇄type⇄ ]} ↑⟨ τ₁⊑τ₂₁ ⟩ ⌾ ↑⟨ τ♯₂⊑η[τ₁] ⟩

_⊓♯_ : type♯ → type♯ → type♯
⊤ ⊓♯ τ = τ
τ ⊓♯ ⊤ = τ
⟨𝔹⟩ ⊓♯ ⟨𝔹⟩ = ⟨𝔹⟩
(x₁ ⟨→⟩ x₂) ⊓♯ (y₁ ⟨→⟩ y₂) = x₁ ⊓♯ y₁ ⟨→⟩ x₂ ⊓♯ y₂
_ ⊓♯ _ = ⊥

left-zero[⊓♯] : ∀ τ → ⊥ ⊓♯ τ ≡ ⊥
left-zero[⊓♯] ⊥ = ↯
left-zero[⊓♯] ⊤ = ↯
left-zero[⊓♯] ⟨𝔹⟩ = ↯
left-zero[⊓♯] (_ ⟨→⟩ _) = ↯

right-zero[⊓♯] : ∀ τ → τ ⊓♯ ⊥ ≡ ⊥
right-zero[⊓♯] ⊥ = ↯
right-zero[⊓♯] ⊤ = ↯
right-zero[⊓♯] ⟨𝔹⟩ = ↯
right-zero[⊓♯] (_ ⟨→⟩ _) = ↯

right-unit[⊓♯] : ∀ τ → τ ⊓♯ ⊤ ≡ τ
right-unit[⊓♯] ⊥ = ↯
right-unit[⊓♯] ⊤ = ↯
right-unit[⊓♯] ⟨𝔹⟩ = ↯
right-unit[⊓♯] (_ ⟨→⟩ _) = ↯

⊓♯-L : ∀ τ₁ τ₂ → τ₁ ⊓♯ τ₂ ⊴ τ₁
⊓♯-L ⊤ _ = ⊤
⊓♯-L τ ⊤ rewrite right-unit[⊓♯] τ = xRx
⊓♯-L ⊥ τ rewrite left-zero[⊓♯] τ = ⊥
⊓♯-L τ ⊥ rewrite right-zero[⊓♯] τ = ⊥
⊓♯-L ⟨𝔹⟩ ⟨𝔹⟩ = ⟨𝔹⟩
⊓♯-L (τ₁ ⟨→⟩ τ₂) (τ₃ ⟨→⟩ τ₄) = ⊓♯-L τ₁ τ₃ ⟨→⟩ ⊓♯-L τ₂ τ₄
⊓♯-L ⟨𝔹⟩ (_ ⟨→⟩ _) = ⊥
⊓♯-L (_ ⟨→⟩ _) ⟨𝔹⟩ = ⊥

⊓♯-R : ∀ τ₁ τ₂ → τ₁ ⊓♯ τ₂ ⊴ τ₂
⊓♯-R ⊤ _ = xRx
⊓♯-R τ ⊤ rewrite right-unit[⊓♯] τ = ⊤
⊓♯-R ⊥ τ rewrite left-zero[⊓♯] τ = ⊥
⊓♯-R τ ⊥ rewrite right-zero[⊓♯] τ = ⊥
⊓♯-R ⟨𝔹⟩ ⟨𝔹⟩ = ⟨𝔹⟩
⊓♯-R (τ₁ ⟨→⟩ τ₂) (τ₃ ⟨→⟩ τ₄) = ⊓♯-R τ₁ τ₃ ⟨→⟩ ⊓♯-R τ₂ τ₄
⊓♯-R ⟨𝔹⟩ (_ ⟨→⟩ _) = ⊥
⊓♯-R (_ ⟨→⟩ _) ⟨𝔹⟩ = ⊥

monotonic[⊓♯] : proper (_⊴_ ⇉ _⊴_ ⇉ _⊴_) _⊓♯_
monotonic[⊓♯] {⊥} {τ₂₁} ⊥ {τ₁₂} {τ₂₂} _ rewrite left-zero[⊓♯] τ₁₂ = ⊥
monotonic[⊓♯] {τ₁₁} {τ₂₁} _ {⊥} {τ₂₂} ⊥ rewrite right-zero[⊓♯] τ₁₁ = ⊥
monotonic[⊓♯] {τ₁₁} {⊤} ⊤ {τ₁₂} {τ₂₂} ⊴₂ = ⊴₂ ⌾ ⊓♯-R τ₁₁ τ₁₂
monotonic[⊓♯] {τ₁₁} {τ₂₁} ⊴₁ {τ₁₂} {⊤} ⊤ rewrite right-unit[⊓♯] τ₂₁ = ⊴₁ ⌾ ⊓♯-L τ₁₁ τ₁₂
monotonic[⊓♯] ⟨𝔹⟩ ⟨𝔹⟩ = ⟨𝔹⟩
monotonic[⊓♯] (⊴₁₁ ⟨→⟩ ⊴₂₁) (⊴₁₂ ⟨→⟩ ⊴₂₂) = monotonic[⊓♯] ⊴₁₁ ⊴₁₂ ⟨→⟩ monotonic[⊓♯] ⊴₂₁ ⊴₂₂
monotonic[⊓♯] ⟨𝔹⟩ (_ ⟨→⟩ _) = ⊥
monotonic[⊓♯] (_ ⟨→⟩ _) ⟨𝔹⟩ = ⊥

[⊓♯] : ⟪ ⇧ type♯ ⇒ ⇧ type♯ ⇒ ⇧ type♯ ⟫
[⊓♯] = witness-x (curry⸢λ↑⸣ $ curry⸢λ↑⸣ id⸢λ↑⸣) $ mk[witness] _⊓♯_ monotonic[⊓♯]

-- (Proposition 7)

sound[⊓♯] : ∀ τ₁ τ₂ → ηᶜ[ ⇄type⇄ ] ⋅ (equate⁺ ⋅ ↑⟨ τ₁ ⟩ ⋅ ↑⟨ τ₂ ⟩) ⊑ [⊓♯] ⋅ (ηᶜ[ ⇄type⇄ ] ⋅ ↑⟨ τ₁ ⟩) ⋅ (ηᶜ[ ⇄type⇄ ] ⋅ ↑⟨ τ₂ ⟩)
sound[⊓♯] ⊥ _ = ↑⟨ ⊥ ⟩
sound[⊓♯] τ ⊥ rewrite right-zero[equate] τ = ↑⟨ ⊥ ⟩
sound[⊓♯] ⟨𝔹⟩ ⟨𝔹⟩ = ↑⟨ ⟨𝔹⟩ ⟩
sound[⊓♯] (τ₁₁ ⟨→⟩ τ₂₁) (τ₁₂ ⟨→⟩ τ₂₂) with sound[⊓♯] τ₁₁ τ₁₂ | sound[⊓♯] τ₂₁ τ₂₂
... | ↑⟨ IH₁ ⟩ | ↑⟨ IH₂ ⟩ = ↑⟨ IH₁ ⟨→⟩ IH₂ ⟩
sound[⊓♯] ⟨𝔹⟩ (_ ⟨→⟩ _) = ↑⟨ ⊥ ⟩
sound[⊓♯] (_ ⟨→⟩ _) ⟨𝔹⟩ = ↑⟨ ⊥ ⟩

complete[⊓♯] : ∀ τ₁ τ₂ → [⊓♯] ⋅ (ηᶜ[ ⇄type⇄ ] ⋅ ↑⟨ τ₁ ⟩) ⋅ (ηᶜ[ ⇄type⇄ ] ⋅ ↑⟨ τ₂ ⟩) ⊑ ηᶜ[ ⇄type⇄ ] ⋅ (equate⁺ ⋅ ↑⟨ τ₁ ⟩ ⋅ ↑⟨ τ₂ ⟩)
complete[⊓♯] ⊥ τ rewrite left-zero[⊓♯] (η τ) = ↑⟨ ⊥ ⟩
complete[⊓♯] τ ⊥ rewrite right-zero[⊓♯] (η τ) = ↑⟨ ⊥ ⟩
complete[⊓♯] ⟨𝔹⟩ ⟨𝔹⟩ = ↑⟨ ⟨𝔹⟩ ⟩
complete[⊓♯] (τ₁₁ ⟨→⟩ τ₂₁) (τ₁₂ ⟨→⟩ τ₂₂) with complete[⊓♯] τ₁₁ τ₁₂ | complete[⊓♯] τ₂₁ τ₂₂
... | ↑⟨ IH₁ ⟩ | ↑⟨ IH₂ ⟩ = ↑⟨ IH₁ ⟨→⟩ IH₂ ⟩ 
complete[⊓♯] ⟨𝔹⟩ (_ ⟨→⟩ _) = ↑⟨ ⊥ ⟩
complete[⊓♯] (_ ⟨→⟩ _) ⟨𝔹⟩ = ↑⟨ ⊥ ⟩

-----------
-- terms --
-----------

data context♯ : Set where
  [] : context♯
  _∷_ : type♯ → context♯ → context♯

data _∈♯_ : type♯ → context♯ → Set where
  Zero : ∀ {Γ τ} → τ ∈♯ τ ∷ Γ
  Suc : ∀ {Γ τ₁ τ₂} → τ₁ ∈♯ Γ → τ₁ ∈♯ τ₂ ∷ Γ

data _⊢♯_ : context♯ → type♯ → Set where
  Bool : ∀ {Γ} → 𝔹 → Γ ⊢♯ ⟨𝔹⟩
  ⟨if⟩_⟨then⟩_⟨else⟩ : ∀ {Γ τ₁ τ₂}
    → Γ ⊢♯ ⟨𝔹⟩
    → Γ ⊢♯ τ₁
    → Γ ⊢♯ τ₂
    → Γ ⊢♯ τ₁ ⊓♯ τ₂
  Var : ∀ {Γ τ}
    → τ ∈♯ Γ
    → Γ ⊢♯ τ
  ⟨λ⟩ : ∀ {Γ τ₁ τ₂}
    → τ₁ ∷ Γ ⊢♯ τ₂
    → Γ ⊢♯ (τ₁ ⟨→⟩ τ₂)
  _⟨⋅⟩_ : ∀ {Γ τ₁ τ₂}
    → Γ ⊢♯ τ₁
    → Γ ⊢♯ τ₂
    → τ₂ ~ dom♯ τ₁
    → Γ ⊢♯ cod♯ τ₁
  _⦂_ : ∀ {Γ τ₁ τ₂}
    → Γ ⊢♯ τ₁
    → τ₁ ~ τ₂
    → Γ ⊢♯ τ₂
