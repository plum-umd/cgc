module AGT.Gradual where

open import Prelude

open import AGT.Precise

infix  14 _⊲♯_
infix  14 _⊢♯_
infix  14 _⊢⦂♯_
infix  14 _⇰⦂♯_
infix  14 _⇰♯_

infixr 15 _⟨→⟩_
infixr 16 ⟨if⟩_⟨then⟩_⟨else⟩_
infixl 17 _⟨⋅⟩_
infixl 18 _⦂⦂_

infixr 22 _⟇♯_
infixr 24 _⟑♯_

infixr 40 _∷_

---------------------------
-- Gradual Type Language --
---------------------------

data type♯ : Set where
  ⊤ : type♯
  Any : type♯
  None : type♯
  ⟨𝔹⟩ : type♯
  _⟨→⟩_ : type♯ → type♯ → type♯

-----------------------------
-- Precision Partial Order --
-----------------------------

data _≼ᵗ♯_ : type♯ → type♯ → Set where
  ⊤ : ∀ {τ} → τ ≼ᵗ♯ ⊤
  Any : Any ≼ᵗ♯ Any
  None : None ≼ᵗ♯ None
  ⟨𝔹⟩ : ⟨𝔹⟩ ≼ᵗ♯ ⟨𝔹⟩
  _⟨→⟩_ : ∀ {τ₁₁ τ₂₁ τ₁₂ τ₂₂}
    → τ₁₁ ≼ᵗ♯ τ₁₂
    → τ₂₁ ≼ᵗ♯ τ₂₂
    → (τ₁₁ ⟨→⟩ τ₂₁) ≼ᵗ♯ (τ₁₂ ⟨→⟩ τ₂₂)

xRx⸢≼ᵗ♯⸣ : ∀ {τ} → τ ≼ᵗ♯ τ
xRx⸢≼ᵗ♯⸣ {⊤} = ⊤
xRx⸢≼ᵗ♯⸣ {Any} = Any
xRx⸢≼ᵗ♯⸣ {None} = None
xRx⸢≼ᵗ♯⸣ {⟨𝔹⟩} = ⟨𝔹⟩
xRx⸢≼ᵗ♯⸣ {τ₁ ⟨→⟩ τ₂} = xRx⸢≼ᵗ♯⸣ ⟨→⟩ xRx⸢≼ᵗ♯⸣

_⊚⸢≼ᵗ♯⸣_ : ∀ {τ₁ τ₂ τ₃} → τ₂ ≼ᵗ♯ τ₃ → τ₁ ≼ᵗ♯ τ₂ → τ₁ ≼ᵗ♯ τ₃
⊤ ⊚⸢≼ᵗ♯⸣ ≼₁ = ⊤
Any ⊚⸢≼ᵗ♯⸣ Any = Any
None ⊚⸢≼ᵗ♯⸣ None = None
⟨𝔹⟩ ⊚⸢≼ᵗ♯⸣ ⟨𝔹⟩ = ⟨𝔹⟩
(≼₁₁ ⟨→⟩ ≼₂₁) ⊚⸢≼ᵗ♯⸣ (≼₁₂ ⟨→⟩ ≼₂₂) = ≼₁₁ ⊚⸢≼ᵗ♯⸣ ≼₁₂ ⟨→⟩ ≼₂₁ ⊚⸢≼ᵗ♯⸣ ≼₂₂

instance
  Reflexive[≼ᵗ♯] : Reflexive _≼ᵗ♯_
  Reflexive[≼ᵗ♯] = record { xRx = xRx⸢≼ᵗ♯⸣ }
  Transitive[≼ᵗ♯] : Transitive _≼ᵗ♯_
  Transitive[≼ᵗ♯] = record { _⊚_ = _⊚⸢≼ᵗ♯⸣_ }
  Precision[type♯] : Precision 0ᴸ type♯
  Precision[type♯] = mk[Precision] _≼ᵗ♯_

---------------------------------
-- Precision Galois Connection --
---------------------------------

ηᵗ : type → type♯
ηᵗ Any = Any
ηᵗ None = None
ηᵗ ⟨𝔹⟩ = ⟨𝔹⟩
ηᵗ (τ₁ ⟨→⟩ τ₂) = ηᵗ τ₁ ⟨→⟩ ηᵗ τ₂

mono[ηᵗ] : proper (_⊑_ ⇉ _⊑_) ηᵗ
mono[ηᵗ] ↯ = xRx

data _∈γᵗ[_] : type → type♯ → Set where
  ⊤ : ∀ {τ} → τ ∈γᵗ[ ⊤ ]
  Any : Any ∈γᵗ[ Any ]
  None : None ∈γᵗ[ None ]
  ⟨𝔹⟩ : ⟨𝔹⟩ ∈γᵗ[ ⟨𝔹⟩ ]
  _⟨→⟩_ : ∀ {τ₁ τ₂ τ₁♯ τ₂♯}
    → τ₁ ∈γᵗ[ τ₁♯ ]
    → τ₂ ∈γᵗ[ τ₂♯ ]
    → (τ₁ ⟨→⟩ τ₂) ∈γᵗ[ τ₁♯ ⟨→⟩ τ₂♯ ]

mono[∈γᵗ] : proper (_⊑_ ⇉ _⊒_ ⇉ [→]) (flip _∈γᵗ[_])
mono[∈γᵗ] ⊤ ↯ τ₁∈τ₂ = ⊤
mono[∈γᵗ] Any ↯ Any = Any
mono[∈γᵗ] None ↯ None = None
mono[∈γᵗ] ⟨𝔹⟩ ↯ ⟨𝔹⟩ = ⟨𝔹⟩
mono[∈γᵗ] (≼₁ ⟨→⟩ ≼₂) ↯ (∈γ₁ ⟨→⟩ ∈γ₂) = mono[∈γᵗ] ≼₁ ↯ ∈γ₁ ⟨→⟩ mono[∈γᵗ] ≼₂ ↯ ∈γ₂

sound[ηγᵗ] : ∀ {τ} → τ ∈γᵗ[ ηᵗ τ ]
sound[ηγᵗ] {Any} = Any
sound[ηγᵗ] {None} = None
sound[ηγᵗ] {⟨𝔹⟩} = ⟨𝔹⟩
sound[ηγᵗ] {τ₁ ⟨→⟩ τ₂} = sound[ηγᵗ] ⟨→⟩ sound[ηγᵗ]

complete[ηγᵗ] : ∀ {τ τ♯} → τ ∈γᵗ[ τ♯ ] → ηᵗ τ ⊑ τ♯
complete[ηγᵗ] ⊤ = ⊤
complete[ηγᵗ] Any = Any
complete[ηγᵗ] None = None
complete[ηγᵗ] ⟨𝔹⟩ = ⟨𝔹⟩
complete[ηγᵗ] (∈γ₁ ⟨→⟩ ∈γ₂) = complete[ηγᵗ] ∈γ₁ ⟨→⟩ complete[ηγᵗ] ∈γ₂

----------------------
-- Galois Injection --
----------------------

-- Proves that η/γ form a stronger correspondance, called a Galois
-- injection.

∃∈γᵗ : ∀ τ♯ → ∃ τ 𝑠𝑡 τ ∈γᵗ[ τ♯ ]
∃∈γᵗ ⊤ = ⟨∃ ⟨𝔹⟩ , ⊤ ⟩
∃∈γᵗ Any = ⟨∃ Any , Any ⟩
∃∈γᵗ None = ⟨∃ None , None ⟩
∃∈γᵗ ⟨𝔹⟩ = ⟨∃ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩
∃∈γᵗ (τ₁♯ ⟨→⟩ τ₂♯) with ∃∈γᵗ τ₁♯ | ∃∈γᵗ τ₂♯
… | ⟨∃ τ₁ , ∈γ₁ ⟩ | ⟨∃ τ₂ , ∈γ₂ ⟩ = ⟨∃ τ₁ ⟨→⟩ τ₂ , ∈γ₁ ⟨→⟩ ∈γ₂ ⟩

injective[∈γᵗ] : ∀ τ₁♯ τ₂♯ → (∀ τ → τ ∈γᵗ[ τ₁♯ ] → τ ∈γᵗ[ τ₂♯ ]) → τ₁♯ ⊑ τ₂♯
injective[∈γᵗ] _ ⊤ _ = ⊤
injective[∈γᵗ] Any Any _ = Any
injective[∈γᵗ] None None _ = None
injective[∈γᵗ] ⟨𝔹⟩ ⟨𝔹⟩ _ = ⟨𝔹⟩
injective[∈γᵗ] (τ₁₁♯ ⟨→⟩ τ₂₁♯) (τ₁₂♯ ⟨→⟩ τ₂₂♯) ⊆₁ = injective[∈γᵗ] τ₁₁♯ τ₁₂♯ F₁ ⟨→⟩ injective[∈γᵗ] τ₂₁♯ τ₂₂♯ F₂
  where
    F₁ : ∀ τ → τ ∈γᵗ[ τ₁₁♯ ] → τ ∈γᵗ[ τ₁₂♯ ]
    F₁ τ₁ ∈γ₁ with ∃∈γᵗ τ₂₁♯
    … | ⟨∃ τ₂ , ∈γ₂ ⟩ with ⊆₁ (τ₁ ⟨→⟩ τ₂) (∈γ₁ ⟨→⟩ ∈γ₂)
    … | ∈γ₁' ⟨→⟩ ∈γ₂' = ∈γ₁'
    F₂ : ∀ τ → τ ∈γᵗ[ τ₂₁♯ ] → τ ∈γᵗ[ τ₂₂♯ ]
    F₂ τ₂ ∈γ₂ with ∃∈γᵗ τ₁₁♯
    … | ⟨∃ τ₁ , ∈γ₁ ⟩ with ⊆₁ (τ₁ ⟨→⟩ τ₂) (∈γ₁ ⟨→⟩ ∈γ₂)
    … | ∈γ₁' ⟨→⟩ ∈γ₂' = ∈γ₂'
injective[∈γᵗ] ⊤ Any ⊆₁ = case ⊆₁ (⟨𝔹⟩ ⟨→⟩ ⟨𝔹⟩) ⊤ 𝑜𝑓 λ ()
injective[∈γᵗ] ⊤ None ⊆₁ = case ⊆₁ (⟨𝔹⟩ ⟨→⟩ ⟨𝔹⟩) ⊤ 𝑜𝑓 λ ()
injective[∈γᵗ] ⊤ ⟨𝔹⟩ ⊆₁ = case ⊆₁ (⟨𝔹⟩ ⟨→⟩ ⟨𝔹⟩) ⊤ 𝑜𝑓 λ ()
injective[∈γᵗ] ⊤ (τ₁ ⟨→⟩ τ₂) ⊆₁ = case ⊆₁ ⟨𝔹⟩ ⊤ 𝑜𝑓 λ ()
injective[∈γᵗ] Any None ⊆₁ = case ⊆₁ Any Any 𝑜𝑓 λ () 
injective[∈γᵗ] Any ⟨𝔹⟩ ⊆₁ = case ⊆₁ Any Any 𝑜𝑓 λ ()
injective[∈γᵗ] Any (_ ⟨→⟩ _) ⊆₁ = case ⊆₁ Any Any 𝑜𝑓 λ ()
injective[∈γᵗ] None Any ⊆₁ = case ⊆₁ None None 𝑜𝑓 λ () 
injective[∈γᵗ] None ⟨𝔹⟩ ⊆₁ = case ⊆₁ None None 𝑜𝑓 λ ()
injective[∈γᵗ] None (_ ⟨→⟩ _) ⊆₁ = case ⊆₁ None None 𝑜𝑓 λ ()
injective[∈γᵗ] ⟨𝔹⟩ Any ⊆₁ = case ⊆₁ ⟨𝔹⟩ ⟨𝔹⟩ 𝑜𝑓 λ ()
injective[∈γᵗ] ⟨𝔹⟩ None ⊆₁ = case ⊆₁ ⟨𝔹⟩ ⟨𝔹⟩ 𝑜𝑓 λ ()
injective[∈γᵗ] ⟨𝔹⟩ (_ ⟨→⟩ _) ⊆₁ = case ⊆₁ ⟨𝔹⟩ ⟨𝔹⟩ 𝑜𝑓 λ ()
injective[∈γᵗ] (τ₁♯ ⟨→⟩ τ₂♯) Any ⊆₁ with ∃∈γᵗ τ₁♯ | ∃∈γᵗ τ₂♯
… | ⟨∃ τ₁ , τ₁∈γ[τ₁♯] ⟩ | ⟨∃ τ₂ , τ₂∈γ[τ₂♯] ⟩ = case ⊆₁ (τ₁ ⟨→⟩ τ₂) (τ₁∈γ[τ₁♯] ⟨→⟩ τ₂∈γ[τ₂♯]) 𝑜𝑓 λ ()
injective[∈γᵗ] (τ₁♯ ⟨→⟩ τ₂♯) None ⊆₁ with ∃∈γᵗ τ₁♯ | ∃∈γᵗ τ₂♯
… | ⟨∃ τ₁ , τ₁∈γ[τ₁♯] ⟩ | ⟨∃ τ₂ , τ₂∈γ[τ₂♯] ⟩ = case ⊆₁ (τ₁ ⟨→⟩ τ₂) (τ₁∈γ[τ₁♯] ⟨→⟩ τ₂∈γ[τ₂♯]) 𝑜𝑓 λ ()
injective[∈γᵗ] (τ₁♯ ⟨→⟩ τ₂♯) ⟨𝔹⟩ ⊆₁ with ∃∈γᵗ τ₁♯ | ∃∈γᵗ τ₂♯
… | ⟨∃ τ₁ , τ₁∈γ[τ₁♯] ⟩ | ⟨∃ τ₂ , τ₂∈γ[τ₂♯] ⟩ = case ⊆₁ (τ₁ ⟨→⟩ τ₂) (τ₁∈γ[τ₁♯] ⟨→⟩ τ₂∈γ[τ₂♯]) 𝑜𝑓 λ ()

--------------------------
-- Consistent Subtyping --
--------------------------

syntax lift-P p τ₁♯ τ₂♯ = τ₁♯ ~[ p ]~ τ₂♯
syntax Lift-P r ∈γ₁ ∈γ₂ = ∈γ₁ ~[[ r ]]~ ∈γ₂
data lift-P (p : type → type → Set) (τ₁♯ : type♯) (τ₂♯ : type♯) : Set where
  Lift-P : ∀ {τ₁ τ₂} → p τ₁ τ₂ → τ₁ ∈γᵗ[ τ₁♯ ] → τ₂ ∈γᵗ[ τ₂♯ ] → lift-P p τ₁♯ τ₂♯

mono[lift-P] : ∀ (p : type → type → Set) → proper (_⊑_ ⇉ _⊑_ ⇉ [→]) (lift-P p)
mono[lift-P] p {τ₁₁♯} {τ₂₁♯} ≽₁ {τ₁₂♯} {τ₂₂♯} ≽₂ (∈γ₁ ~[[ p[τ₁,τ₂] ]]~ ∈γ₂) = Lift-P p[τ₁,τ₂] (mono[∈γᵗ] ≽₁ ↯ ∈γ₁) (mono[∈γᵗ] ≽₂ ↯ ∈γ₂)

data is[⊤] : type♯ → Set where
  ⊤ : is[⊤] ⊤

data not[⊤] : type♯ → Set where
  Any : not[⊤] Any
  None : not[⊤] None
  ⟨𝔹⟩ : not[⊤] ⟨𝔹⟩
  [⟨→⟩] : ∀ {τ₁ τ₂} → not[⊤] (τ₁ ⟨→⟩ τ₂)

dec[⊤] : ∀ τ → is[⊤] τ ∨ not[⊤] τ
dec[⊤] ⊤ = Inl ⊤
dec[⊤] Any = Inr Any
dec[⊤] None = Inr None
dec[⊤] ⟨𝔹⟩ = Inr ⟨𝔹⟩
dec[⊤] (_ ⟨→⟩ _) = Inr [⟨→⟩]

data _⋖♯_ : type♯ → type♯ → Set where
  ⊤Rτ : ∀ {τ} → ⊤ ⋖♯ τ
  τR⊤ : ∀ {τ} → τ ⋖♯ ⊤
  Any : ∀ {τ} → not[⊤] τ → τ ⋖♯ Any
  None : ∀ {τ} → not[⊤] τ → None ⋖♯ τ
  ⟨𝔹⟩ : ⟨𝔹⟩ ⋖♯ ⟨𝔹⟩
  _⟨→⟩_ : ∀ {τ₁₁ τ₂₁ τ₁₂ τ₂₂}
    → τ₁₂ ⋖♯ τ₁₁
    → τ₂₁ ⋖♯ τ₂₂
    → (τ₁₁ ⟨→⟩ τ₂₁) ⋖♯ (τ₁₂ ⟨→⟩ τ₂₂)

xRx⸢⋖♯⸣ : reflexive _⋖♯_
xRx⸢⋖♯⸣ {⊤} = ⊤Rτ
xRx⸢⋖♯⸣ {Any} = Any Any
xRx⸢⋖♯⸣ {None} = None None
xRx⸢⋖♯⸣ {⟨𝔹⟩} = ⟨𝔹⟩
xRx⸢⋖♯⸣ {τ₁ ⟨→⟩ τ₂} = xRx⸢⋖♯⸣ ⟨→⟩ xRx⸢⋖♯⸣

instance
  Reflexive[⋖♯] : Reflexive _⋖♯_
  Reflexive[⋖♯] = record { xRx = xRx⸢⋖♯⸣ }

⋖♯Any : ∀ {τ} → τ ⋖♯ Any
⋖♯Any {⊤} = ⊤Rτ
⋖♯Any {Any} = Any Any
⋖♯Any {None} = Any None
⋖♯Any {⟨𝔹⟩} = Any ⟨𝔹⟩
⋖♯Any {_ ⟨→⟩ _} = Any [⟨→⟩]

⋖♯None : ∀ {τ} → None ⋖♯ τ
⋖♯None {⊤} = τR⊤
⋖♯None {Any} = Any None
⋖♯None {None} = None None
⋖♯None {⟨𝔹⟩} = None ⟨𝔹⟩
⋖♯None {_ ⟨→⟩ _} = None [⟨→⟩]

mono[⋖♯] : proper (_⊑_ ⇉ _⊑_ ⇉ [→]) _⋖♯_
mono[⋖♯] _ Any (Any _) = ⋖♯Any
mono[⋖♯] None _ (None _) = ⋖♯None
mono[⋖♯] ⟨𝔹⟩ ⟨𝔹⟩ ⟨𝔹⟩ = ⟨𝔹⟩
mono[⋖♯] (≼₁₁ ⟨→⟩ ≼₂₁) (≼₁₂ ⟨→⟩ ≼₂₂) (⋖₁ ⟨→⟩ ⋖₂) = mono[⋖♯] ≼₁₂ ≼₁₁ ⋖₁ ⟨→⟩ mono[⋖♯] ≼₂₁ ≼₂₂ ⋖₂
mono[⋖♯] ⊤ _ _ = ⊤Rτ
mono[⋖♯] _ ⊤ _ = τR⊤

consistent[⋖♯] : ∀ {τ₁♯ τ₂♯} → (τ₁♯ ⋖♯ τ₂♯) ↔ (τ₁♯ ~[ _⋖_ ]~ τ₂♯)
consistent[⋖♯] = ⟨ LHS , RHS ⟩
  where
    LHS : ∀ {τ₁♯ τ₂♯} → τ₁♯ ⋖♯ τ₂♯ → τ₁♯ ~[ _⋖_ ]~ τ₂♯
    LHS {.⊤} {τ₂♯} ⊤Rτ with ∃∈γᵗ τ₂♯
    … | ⟨∃ τ , τ∈γ[τ₂♯] ⟩ = ⊤ ~[[ xRx ]]~ τ∈γ[τ₂♯]
    LHS {τ₁♯} {.⊤} τR⊤ with ∃∈γᵗ τ₁♯
    … | ⟨∃ τ , τ∈γ[τ₁♯] ⟩ = τ∈γ[τ₁♯] ~[[ xRx ]]~ ⊤
    LHS {τ₁♯} {.Any} (Any _) with ∃∈γᵗ τ₁♯
    … | ⟨∃ τ , τ∈γ[τ₁♯] ⟩ = τ∈γ[τ₁♯] ~[[ Any ]]~ Any
    LHS {.None} {τ₂♯} (None _) with ∃∈γᵗ τ₂♯
    … | ⟨∃ τ , τ∈γ[τ₂♯] ⟩ = None ~[[ None ]]~ τ∈γ[τ₂♯]
    LHS ⟨𝔹⟩ = ⟨𝔹⟩ ~[[ ⟨𝔹⟩ ]]~ ⟨𝔹⟩
    LHS (⋖♯₁ ⟨→⟩ ⋖♯₂) with LHS ⋖♯₁ | LHS ⋖♯₂
    … | τ₁₁∈γ[τ₁₁♯] ~[[ τ₁₁<:τ₁₂ ]]~ τ₁₂∈γ[τ₁₂♯] | τ₂₁∈γ[τ₂₁♯] ~[[ τ₂₁<:τ₂₂ ]]~ τ₂₂∈γ[τ₂₂♯] =
      (τ₁₂∈γ[τ₁₂♯] ⟨→⟩ τ₂₁∈γ[τ₂₁♯]) ~[[ τ₁₁<:τ₁₂ ⟨→⟩ τ₂₁<:τ₂₂ ]]~ (τ₁₁∈γ[τ₁₁♯] ⟨→⟩ τ₂₂∈γ[τ₂₂♯])
    RHS : ∀ {τ₁♯ τ₂♯} → τ₁♯ ~[ _⋖_ ]~ τ₂♯ → τ₁♯ ⋖♯ τ₂♯ 
    RHS {τ₁♯} {.Any} (Lift-P Any ∈γ₁ Any) with dec[⊤] τ₁♯
    RHS {.⊤} {.Any} (Lift-P Any ∈γ₁ Any) | Inl ⊤ = ⊤Rτ
    … | Inr not[⊤] = Any not[⊤]
    RHS {.None} {τ₂♯} (Lift-P None None ∈γ₂) with dec[⊤] τ₂♯
    RHS {.None} {.⊤} (Lift-P None None ∈γ₂) | Inl ⊤ = τR⊤
    … | Inr not[⊤] = None not[⊤]
    RHS (Lift-P ⟨𝔹⟩ ⟨𝔹⟩ ⟨𝔹⟩) = ⟨𝔹⟩
    RHS (Lift-P (<:₁ ⟨→⟩ <:₂) (∈γ₁₁ ⟨→⟩ ∈γ₂₁) (∈γ₁₂ ⟨→⟩ ∈γ₂₂)) = RHS (Lift-P <:₁ ∈γ₁₂ ∈γ₁₁) ⟨→⟩ RHS (Lift-P <:₂ ∈γ₂₁ ∈γ₂₂)
    RHS (Lift-P _ _ ⊤) = τR⊤
    RHS (Lift-P _ ⊤ _) = ⊤Rτ

---------------------------
-- Subtype Join and Meet --
---------------------------

mutual
  _⟇♯_ : type♯ → type♯ → type♯
  ⊤ ⟇♯ _ = ⊤
  _ ⟇♯ ⊤ = ⊤
  Any ⟇♯ _ = Any
  _ ⟇♯ Any = Any
  None ⟇♯ τ = τ
  τ ⟇♯ None = τ
  ⟨𝔹⟩ ⟇♯ ⟨𝔹⟩ = ⟨𝔹⟩
  (τ₁₁ ⟨→⟩ τ₂₁) ⟇♯ (τ₁₂ ⟨→⟩ τ₂₂) = (τ₁₁ ⟑♯ τ₁₂) ⟨→⟩ (τ₂₁ ⟇♯ τ₂₂)
  ⟨𝔹⟩ ⟇♯ (_ ⟨→⟩ _) = Any
  (_ ⟨→⟩ _) ⟇♯ ⟨𝔹⟩ = Any

  _⟑♯_ : type♯ → type♯ → type♯
  ⊤ ⟑♯ _ = ⊤
  _ ⟑♯ ⊤ = ⊤
  Any ⟑♯ τ = τ
  τ ⟑♯ Any = τ
  None ⟑♯ _ = None
  _ ⟑♯ None = None
  ⟨𝔹⟩ ⟑♯ ⟨𝔹⟩ = ⟨𝔹⟩
  (τ₁₁ ⟨→⟩ τ₂₁) ⟑♯ (τ₁₂ ⟨→⟩ τ₂₂) = (τ₁₁ ⟇♯ τ₁₂) ⟨→⟩ (τ₂₁ ⟑♯ τ₂₂)
  ⟨𝔹⟩ ⟑♯ (y ⟨→⟩ y₁) = None
  (x ⟨→⟩ x₁) ⟑♯ ⟨𝔹⟩ = None

zero[⟇♯]/⊤ : ∀ τ → ⊤ ⟇♯ τ ≡ ⊤ ∧ τ ⟇♯ ⊤ ≡ ⊤
zero[⟇♯]/⊤ ⊤ = ⟨ ↯ , ↯ ⟩
zero[⟇♯]/⊤ Any = ⟨ ↯ , ↯ ⟩
zero[⟇♯]/⊤ None = ⟨ ↯ , ↯ ⟩
zero[⟇♯]/⊤ ⟨𝔹⟩ = ⟨ ↯ , ↯ ⟩
zero[⟇♯]/⊤ (_ ⟨→⟩ _) = ⟨ ↯ , ↯ ⟩

zero[⟑♯]/⊤ : ∀ τ → ⊤ ⟑♯ τ ≡ ⊤ ∧ τ ⟑♯ ⊤ ≡ ⊤
zero[⟑♯]/⊤ ⊤ = ⟨ ↯ , ↯ ⟩
zero[⟑♯]/⊤ Any = ⟨ ↯ , ↯ ⟩
zero[⟑♯]/⊤ None = ⟨ ↯ , ↯ ⟩
zero[⟑♯]/⊤ ⟨𝔹⟩ = ⟨ ↯ , ↯ ⟩
zero[⟑♯]/⊤ (_ ⟨→⟩ _) = ⟨ ↯ , ↯ ⟩

unit[⟇♯] : ∀ τ → None ⟇♯ τ ≡ τ ∧ τ ⟇♯ None ≡ τ
unit[⟇♯] ⊤ = ⟨ ↯ , ↯ ⟩
unit[⟇♯] Any = ⟨ ↯ , ↯ ⟩
unit[⟇♯] None = ⟨ ↯ , ↯ ⟩
unit[⟇♯] ⟨𝔹⟩ = ⟨ ↯ , ↯ ⟩
unit[⟇♯] (_ ⟨→⟩ _) = ⟨ ↯ , ↯ ⟩

zero[⟇♯]/¬⊤ : ∀ {τ} → not[⊤] τ → Any ⟇♯ τ ≡ Any ∧ τ ⟇♯ Any ≡ Any
zero[⟇♯]/¬⊤ Any = ⟨ ↯ , ↯ ⟩
zero[⟇♯]/¬⊤ None = ⟨ ↯ , ↯ ⟩
zero[⟇♯]/¬⊤ ⟨𝔹⟩ = ⟨ ↯ , ↯ ⟩
zero[⟇♯]/¬⊤ [⟨→⟩] = ⟨ ↯ , ↯ ⟩

unit[⟑♯] : ∀ τ → Any ⟑♯ τ ≡ τ ∧ τ ⟑♯ Any ≡ τ
unit[⟑♯] ⊤ = ⟨ ↯ , ↯ ⟩
unit[⟑♯] Any = ⟨ ↯ , ↯ ⟩
unit[⟑♯] None = ⟨ ↯ , ↯ ⟩
unit[⟑♯] ⟨𝔹⟩ = ⟨ ↯ , ↯ ⟩
unit[⟑♯] (_ ⟨→⟩ _) = ⟨ ↯ , ↯ ⟩

zero[⟑♯]/¬⊤ : ∀ {τ} → not[⊤] τ → None ⟑♯ τ ≡ None ∧ τ ⟑♯ None ≡ None
zero[⟑♯]/¬⊤ Any = ⟨ ↯ , ↯ ⟩
zero[⟑♯]/¬⊤ None = ⟨ ↯ , ↯ ⟩
zero[⟑♯]/¬⊤ ⟨𝔹⟩ = ⟨ ↯ , ↯ ⟩
zero[⟑♯]/¬⊤ [⟨→⟩] = ⟨ ↯ , ↯ ⟩

strengthen[not[⊤]] : ∀ {τ₁ τ₂ : type♯} → τ₁ ⊑ τ₂ → not[⊤] τ₂ → not[⊤] τ₁
strengthen[not[⊤]] Any Any = Any
strengthen[not[⊤]] None None = None
strengthen[not[⊤]] ⟨𝔹⟩ ⟨𝔹⟩ = ⟨𝔹⟩
strengthen[not[⊤]] (_ ⟨→⟩ _) [⟨→⟩] = [⟨→⟩]

mutual
  mono[⟇♯] : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) _⟇♯_
  mono[⟇♯] {_} {τ₁} _ {_} {τ₂} _ with dec[⊤] τ₁ | dec[⊤] τ₂
  mono[⟇♯] _ _ | Inl ⊤ | _ = ⊤
  mono[⟇♯] {_} {τ₁} _ _ | _ | Inl ⊤ rewrite π₂ (zero[⟇♯]/⊤ τ₁) = ⊤
  mono[⟇♯] Any ≼₂ | Inr Any | Inr not[⊤]₂ rewrite π₁ (zero[⟇♯]/¬⊤ (strengthen[not[⊤]] ≼₂ not[⊤]₂)) | π₁ (zero[⟇♯]/¬⊤ not[⊤]₂) = Any
  mono[⟇♯] ≼₁ Any | Inr not[⊤]₁ | Inr Any rewrite π₂ (zero[⟇♯]/¬⊤ (strengthen[not[⊤]] ≼₁ not[⊤]₁)) | π₂ (zero[⟇♯]/¬⊤ not[⊤]₁) = Any
  mono[⟇♯] None {τ₁} {τ₂} ≼₂ | Inr None | Inr _ rewrite π₁ (unit[⟇♯] τ₁) | π₁ (unit[⟇♯] τ₂) = ≼₂
  mono[⟇♯] {τ₁} {τ₂} ≼₁ None | Inr _ | Inr None rewrite π₂ (unit[⟇♯] τ₁) | π₂ (unit[⟇♯] τ₂) = ≼₁
  mono[⟇♯] ⟨𝔹⟩ ⟨𝔹⟩ | Inr ⟨𝔹⟩ | Inr ⟨𝔹⟩ = ⟨𝔹⟩
  mono[⟇♯] (≼₁₁ ⟨→⟩ ≼₂₁) (≼₁₂ ⟨→⟩ ≼₂₂) | Inr [⟨→⟩] | Inr [⟨→⟩] = mono[⟑♯] ≼₁₁ ≼₁₂ ⟨→⟩ mono[⟇♯] ≼₂₁ ≼₂₂
  mono[⟇♯] ⟨𝔹⟩ (_ ⟨→⟩ _) | Inr ⟨𝔹⟩ | Inr [⟨→⟩] = Any
  mono[⟇♯] (_ ⟨→⟩ _) ⟨𝔹⟩ | Inr [⟨→⟩] | Inr ⟨𝔹⟩ = Any

  mono[⟑♯] : proper (_⊑_ ⇉ _⊑_ ⇉ _⊑_) _⟑♯_
  mono[⟑♯] {_} {τ₁} _ {_} {τ₂} _ with dec[⊤] τ₁ | dec[⊤] τ₂
  mono[⟑♯] _ _ | Inl ⊤ | _ = ⊤
  mono[⟑♯] {_} {τ₁} _ _ | _ | Inl ⊤ rewrite π₂ (zero[⟑♯]/⊤ τ₁) = ⊤
  mono[⟑♯] Any {τ₁} {τ₂} ≼₂ | Inr Any | Inr _ rewrite π₁ (unit[⟑♯] τ₁) | π₁ (unit[⟑♯] τ₂) = ≼₂
  mono[⟑♯] {τ₁} {τ₂} ≼₁ Any | Inr _ | Inr Any rewrite π₂ (unit[⟑♯] τ₁) | π₂ (unit[⟑♯] τ₂) = ≼₁
  mono[⟑♯] None ≼₂ | Inr None | Inr not[⊤]₂ rewrite π₁ (zero[⟑♯]/¬⊤ (strengthen[not[⊤]] ≼₂ not[⊤]₂)) | π₁ (zero[⟑♯]/¬⊤ not[⊤]₂) = None
  mono[⟑♯] ≼₁ None | Inr not[⊤]₁ | Inr None rewrite π₂ (zero[⟑♯]/¬⊤ (strengthen[not[⊤]] ≼₁ not[⊤]₁)) | π₂ (zero[⟑♯]/¬⊤ not[⊤]₁) = None
  mono[⟑♯] ⟨𝔹⟩ ⟨𝔹⟩ | Inr ⟨𝔹⟩ | Inr ⟨𝔹⟩ = ⟨𝔹⟩
  mono[⟑♯] (≼₁₁ ⟨→⟩ ≼₂₁) (≼₁₂ ⟨→⟩ ≼₂₂) | Inr [⟨→⟩] | Inr [⟨→⟩] = mono[⟇♯] ≼₁₁ ≼₁₂ ⟨→⟩ mono[⟑♯] ≼₂₁ ≼₂₂
  mono[⟑♯] ⟨𝔹⟩ (_ ⟨→⟩ _) | Inr ⟨𝔹⟩ | Inr [⟨→⟩] = None
  mono[⟑♯] (_ ⟨→⟩ _) ⟨𝔹⟩ | Inr [⟨→⟩] | Inr ⟨𝔹⟩ = None

not[⊤][η] : ∀ τ → not[⊤] (ηᵗ τ)
not[⊤][η] Any = Any
not[⊤][η] None = None
not[⊤][η] ⟨𝔹⟩ = ⟨𝔹⟩
not[⊤][η] (_ ⟨→⟩ _) = [⟨→⟩]

mutual
  correct[⟇♯] : ∀ τ₁ τ₂ → ηᵗ (τ₁ ⟇ τ₂) ≡ (ηᵗ τ₁ ⟇♯ ηᵗ τ₂)
  correct[⟇♯] Any τ₂ rewrite π₁ (zero[⟇♯]/¬⊤ (not[⊤][η] τ₂)) = ↯
  correct[⟇♯] τ₁ Any rewrite π₂ (zero[⟇] τ₁) | π₂ (zero[⟇♯]/¬⊤ (not[⊤][η] τ₁)) = ↯
  correct[⟇♯] None τ₂ rewrite π₁ (unit[⟇] τ₂) | π₁ (unit[⟇♯] (ηᵗ τ₂)) = ↯
  correct[⟇♯] τ₁ None rewrite π₂ (unit[⟇] τ₁) | π₂ (unit[⟇♯] (ηᵗ τ₁)) = ↯
  correct[⟇♯] ⟨𝔹⟩ ⟨𝔹⟩ = ↯
  correct[⟇♯] (τ₁₁ ⟨→⟩ τ₂₁) (τ₁₂ ⟨→⟩ τ₂₂) rewrite correct[⟑♯] τ₁₁ τ₁₂ | correct[⟇♯] τ₂₁ τ₂₂ = ↯
  correct[⟇♯] ⟨𝔹⟩ (_ ⟨→⟩ _) = ↯
  correct[⟇♯] (_ ⟨→⟩ _) ⟨𝔹⟩ = ↯

  correct[⟑♯] : ∀ τ₁ τ₂ → ηᵗ (τ₁ ⟑ τ₂) ≡ (ηᵗ τ₁ ⟑♯ ηᵗ τ₂)
  correct[⟑♯] Any τ₂ rewrite π₁ (unit[⟑♯] (ηᵗ τ₂)) = ↯
  correct[⟑♯] τ₁ Any rewrite π₂ (unit[⟑] τ₁) | π₂ (unit[⟑♯] (ηᵗ τ₁)) = ↯
  correct[⟑♯] None τ₂ rewrite π₁ (zero[⟑] τ₂) | π₁ (zero[⟑♯]/¬⊤ (not[⊤][η] τ₂)) = ↯
  correct[⟑♯] τ₁ None rewrite π₂ (zero[⟑] τ₁) | π₂ (zero[⟑♯]/¬⊤ (not[⊤][η] τ₁)) = ↯
  correct[⟑♯] ⟨𝔹⟩ ⟨𝔹⟩ = ↯
  correct[⟑♯] (τ₁₁ ⟨→⟩ τ₂₁) (τ₁₂ ⟨→⟩ τ₂₂) rewrite correct[⟇♯] τ₁₁ τ₁₂ | correct[⟑♯] τ₂₁ τ₂₂ = ↯
  correct[⟑♯] ⟨𝔹⟩ (_ ⟨→⟩ _) = ↯
  correct[⟑♯] (_ ⟨→⟩ _) ⟨𝔹⟩ = ↯

mutual
  weaken[⋖♯][_] : ∀ {τ₁ τ₂} τ₃ → τ₁ ⋖♯ τ₂ → τ₁ ⋖♯ (τ₂ ⟇♯ τ₃) ∧ τ₁ ⋖♯ (τ₃ ⟇♯ τ₂)
  weaken[⋖♯][ _ ] ⊤Rτ = ⟨ ⊤Rτ , ⊤Rτ ⟩
  weaken[⋖♯][ τ₃ ] τR⊤ rewrite π₂ (zero[⟇♯]/⊤ τ₃) = ⟨ τR⊤ , τR⊤ ⟩
  weaken[⋖♯][ τ₃ ] (Any _) with dec[⊤] τ₃
  weaken[⋖♯][ .⊤ ] (Any _) | Inl ⊤ = ⟨ τR⊤ , τR⊤ ⟩
  weaken[⋖♯][ _ ] (Any _) | Inr not[⊤]₃ rewrite π₁ (zero[⟇♯]/¬⊤ not[⊤]₃) | π₂ (zero[⟇♯]/¬⊤ not[⊤]₃) = ⟨ ⋖♯Any , ⋖♯Any ⟩
  weaken[⋖♯][ _ ] (None _) = ⟨ ⋖♯None , ⋖♯None ⟩
  weaken[⋖♯][ Any ] ⟨𝔹⟩ = ⟨ Any ⟨𝔹⟩ , Any ⟨𝔹⟩ ⟩
  weaken[⋖♯][ None ] ⟨𝔹⟩ = ⟨ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩
  weaken[⋖♯][ ⟨𝔹⟩ ] ⟨𝔹⟩ = ⟨ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩
  weaken[⋖♯][ _ ⟨→⟩ _ ] ⟨𝔹⟩ = ⟨ Any ⟨𝔹⟩ , Any ⟨𝔹⟩ ⟩
  weaken[⋖♯][ Any ] (_ ⟨→⟩ _) = ⟨ Any [⟨→⟩] , Any [⟨→⟩] ⟩
  weaken[⋖♯][ None ] (⋖₁ ⟨→⟩ ⋖₂) = ⟨ ⋖₁ ⟨→⟩ ⋖₂ , ⋖₁ ⟨→⟩ ⋖₂ ⟩
  weaken[⋖♯][ ⟨𝔹⟩ ] (_ ⟨→⟩ _) = ⟨ Any [⟨→⟩] , Any [⟨→⟩] ⟩
  weaken[⋖♯][ τ₁ ⟨→⟩ τ₂ ] (⋖₁ ⟨→⟩ ⋖₂) = ⟨ π₁ (strengthen[⋖♯][ τ₁ ] ⋖₁) ⟨→⟩ π₁ (weaken[⋖♯][ τ₂ ] ⋖₂) , π₂ (strengthen[⋖♯][ τ₁ ] ⋖₁) ⟨→⟩ π₂ (weaken[⋖♯][ τ₂ ] ⋖₂) ⟩
  weaken[⋖♯][_] {_} {τ₂} ⊤ _ rewrite π₂ (zero[⟇♯]/⊤ τ₂) = ⟨ τR⊤ , τR⊤ ⟩

  strengthen[⋖♯][_] : ∀ {τ₁ τ₂} τ₃ → τ₁ ⋖♯ τ₂ → (τ₁ ⟑♯ τ₃) ⋖♯ τ₂ ∧ (τ₃ ⟑♯ τ₁) ⋖♯ τ₂
  strengthen[⋖♯][ τ₃ ] ⊤Rτ rewrite π₂ (zero[⟑♯]/⊤ τ₃) = ⟨ ⊤Rτ , ⊤Rτ ⟩
  strengthen[⋖♯][ _ ] τR⊤ = ⟨ τR⊤ , τR⊤ ⟩
  strengthen[⋖♯][ τ₃ ] (Any _) = ⟨ ⋖♯Any , ⋖♯Any ⟩
  strengthen[⋖♯][ τ₃ ] (None _) with dec[⊤] τ₃
  strengthen[⋖♯][ .⊤ ] (None _) | Inl ⊤ = ⟨ ⊤Rτ , ⊤Rτ ⟩
  strengthen[⋖♯][ _ ] (None _) | Inr not[⊤]₃ rewrite π₁ (zero[⟑♯]/¬⊤ not[⊤]₃) | π₂ (zero[⟑♯]/¬⊤ not[⊤]₃) = ⟨ ⋖♯None , ⋖♯None ⟩
  strengthen[⋖♯][ Any ] ⟨𝔹⟩ = ⟨ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩
  strengthen[⋖♯][ None ] ⟨𝔹⟩ = ⟨ None ⟨𝔹⟩ , None ⟨𝔹⟩ ⟩
  strengthen[⋖♯][ ⟨𝔹⟩ ] ⟨𝔹⟩ = ⟨ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩
  strengthen[⋖♯][ _ ⟨→⟩ _ ] ⟨𝔹⟩ = ⟨ None ⟨𝔹⟩ , None ⟨𝔹⟩ ⟩
  strengthen[⋖♯][ Any ] (⋖₁ ⟨→⟩ ⋖₂) = ⟨ ⋖₁ ⟨→⟩ ⋖₂ , ⋖₁ ⟨→⟩ ⋖₂ ⟩
  strengthen[⋖♯][ None ] (_ ⟨→⟩ _) = ⟨ None [⟨→⟩] , None [⟨→⟩] ⟩
  strengthen[⋖♯][ ⟨𝔹⟩ ] (_ ⟨→⟩ _) = ⟨ None [⟨→⟩] , None [⟨→⟩] ⟩
  strengthen[⋖♯][ τ₁ ⟨→⟩ τ₂ ] (⋖₀ ⟨→⟩ ⋖₁) = ⟨ π₁ (weaken[⋖♯][ τ₁ ] ⋖₀) ⟨→⟩ π₁ (strengthen[⋖♯][ τ₂ ] ⋖₁) , π₂ (weaken[⋖♯][ τ₁ ] ⋖₀) ⟨→⟩ π₂ (strengthen[⋖♯][ τ₂ ] ⋖₁) ⟩
  strengthen[⋖♯][_] {τ₁} ⊤ _ rewrite π₂ (zero[⟑♯]/⊤ τ₁) = ⟨ ⊤Rτ , ⊤Rτ ⟩

weaken[⋖♯]/L[_] : ∀ {τ₁ τ₂} τ₃ → τ₁ ⋖♯ τ₂ → τ₁ ⋖♯ (τ₂ ⟇♯ τ₃)
weaken[⋖♯]/L[ τ ] ⋖₀ = π₁ (weaken[⋖♯][ τ ] ⋖₀)

weaken[⋖♯]/R[_] : ∀ {τ₁ τ₂} τ₃ → τ₁ ⋖♯ τ₂ → τ₁ ⋖♯ (τ₃ ⟇♯ τ₂)
weaken[⋖♯]/R[ τ ] ⋖₀ = π₂ (weaken[⋖♯][ τ ] ⋖₀)

strengthen[⋖♯]/L[_] : ∀ {τ₁ τ₂} τ₃ → τ₁ ⋖♯ τ₂ → (τ₁ ⟑♯ τ₃) ⋖♯ τ₂
strengthen[⋖♯]/L[ τ ] ⋖₀ = π₁ (strengthen[⋖♯][ τ ] ⋖₀)

strengthen[⋖♯]/R[_] : ∀ {τ₁ τ₂} τ₃ → τ₁ ⋖♯ τ₂ → (τ₃ ⟑♯ τ₁) ⋖♯ τ₂
strengthen[⋖♯]/R[ τ ] ⋖₀ = π₂ (strengthen[⋖♯][ τ ] ⋖₀)

---------------
-- Interiors --
---------------

data ⟨_,_⟩∈I⟨_,_⟩ : type♯ → type♯ → type♯ → type♯ → Set where
  ⊤ :
    ⟨ ⊤ , ⊤ ⟩∈I⟨ ⊤ , ⊤ ⟩
  Any,⊤ :
    ⟨ Any , Any ⟩∈I⟨ Any , ⊤ ⟩
  τ,Any : ∀ {τ}
    → ⟨ τ , Any ⟩∈I⟨ τ , Any ⟩
  None,τ : ∀ {τ}
    → ⟨ None , τ ⟩∈I⟨ None , τ ⟩
  ⊤,None :
    ⟨ None , None ⟩∈I⟨ ⊤ , None ⟩
  ⟨𝔹⟩,⊤ :
    ⟨ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩∈I⟨ ⟨𝔹⟩ , ⊤ ⟩
  ⊤,⟨𝔹⟩ :
    ⟨ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩∈I⟨ ⊤ , ⟨𝔹⟩ ⟩
  ⟨𝔹⟩ :
    ⟨ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩∈I⟨ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩
  _⟨→⟩⊤_ : ∀ {τ₁₁ τ₂₁ τ₁₁ᴵ τ₂₁ᴵ τ₁₂ᴵ τ₂₂ᴵ} 
    → ⟨ τ₁₂ᴵ , τ₁₁ᴵ ⟩∈I⟨ ⊤ , τ₁₁ ⟩
    → ⟨ τ₂₁ᴵ , τ₂₂ᴵ ⟩∈I⟨ τ₂₁ , ⊤ ⟩
    → ⟨ τ₁₁ᴵ ⟨→⟩ τ₂₁ᴵ , τ₁₂ᴵ ⟨→⟩ τ₂₂ᴵ ⟩∈I⟨ τ₁₁ ⟨→⟩ τ₂₁ , ⊤ ⟩
  _⊤⟨→⟩_ : ∀ {τ₁₂ τ₂₂ τ₁₁ᴵ τ₂₁ᴵ τ₁₂ᴵ τ₂₂ᴵ}
    → ⟨ τ₁₂ᴵ , τ₁₁ᴵ ⟩∈I⟨ τ₁₂ , ⊤ ⟩
    → ⟨ τ₂₁ᴵ , τ₂₂ᴵ ⟩∈I⟨ ⊤ , τ₂₂ ⟩
    → ⟨ τ₁₁ᴵ ⟨→⟩ τ₂₁ᴵ , τ₁₂ᴵ ⟨→⟩ τ₂₂ᴵ ⟩∈I⟨ ⊤ , τ₁₂ ⟨→⟩ τ₂₂ ⟩
  _⟨→⟩_ : ∀ {τ₁₁ τ₂₁ τ₁₂ τ₂₂ τ₁₁ᴵ τ₂₁ᴵ τ₁₂ᴵ τ₂₂ᴵ}
    → ⟨ τ₁₂ᴵ , τ₁₁ᴵ ⟩∈I⟨ τ₁₂ , τ₁₁ ⟩
    → ⟨ τ₂₁ᴵ , τ₂₂ᴵ ⟩∈I⟨ τ₂₁ , τ₂₂ ⟩
    → ⟨ τ₁₁ᴵ ⟨→⟩ τ₂₁ᴵ , τ₁₂ᴵ ⟨→⟩ τ₂₂ᴵ ⟩∈I⟨ τ₁₁ ⟨→⟩ τ₂₁ , τ₁₂ ⟨→⟩ τ₂₂ ⟩

data ∃I⟨_,_⟩ : type♯ → type♯ → Set where
  ∃I : ∀ {τ₁ τ₂ τ₁ᴵ τ₂ᴵ} → ⟨ τ₁ᴵ , τ₂ᴵ ⟩∈I⟨ τ₁ , τ₂ ⟩ → ∃I⟨ τ₁ , τ₂ ⟩

correct[I] : ∀ {τ₁ τ₂} → τ₁ ⋖♯ τ₂ ↔ ∃I⟨ τ₁ , τ₂ ⟩
correct[I] = ⟨ LHS , RHS ⟩
  where
    LHS : ∀ {τ₁ τ₂} → τ₁ ⋖♯ τ₂ → ∃I⟨ τ₁ , τ₂ ⟩
    LHS {⊤} {⊤} ⊤Rτ = ∃I ⊤
    LHS {⊤} {Any} ⊤Rτ = ∃I τ,Any
    LHS {⊤} {None} ⊤Rτ = ∃I ⊤,None
    LHS {⊤} {⟨𝔹⟩} ⊤Rτ = ∃I ⊤,⟨𝔹⟩
    LHS {⊤} {τ₁ ⟨→⟩ τ₂} ⊤Rτ with LHS {τ₁} {⊤} τR⊤ | LHS {⊤} {τ₂} ⊤Rτ
    … | ∃I I₁ | ∃I I₂ = ∃I (I₁ ⊤⟨→⟩ I₂)
    LHS {⊤} {⊤} τR⊤ = ∃I ⊤
    LHS {Any} {⊤} τR⊤ = ∃I Any,⊤
    LHS {None} {⊤} τR⊤ = ∃I None,τ
    LHS {⟨𝔹⟩} {⊤} τR⊤ = ∃I ⟨𝔹⟩,⊤
    LHS {τ₁ ⟨→⟩ τ₂} {⊤} τR⊤ with LHS {⊤} {τ₁} ⊤Rτ | LHS {τ₂} {⊤} τR⊤
    … | ∃I I₁ | ∃I I₂ = ∃I (I₁ ⟨→⟩⊤ I₂)
    LHS {τ₁} {Any} (Any _) = ∃I τ,Any
    LHS {None} {τ₂} (None _) = ∃I None,τ
    LHS ⟨𝔹⟩ = ∃I ⟨𝔹⟩
    LHS (⋖♯₁ ⟨→⟩ ⋖♯₂) with LHS ⋖♯₁ | LHS ⋖♯₂
    … | ∃I I₁ | ∃I I₂ = ∃I (I₁ ⟨→⟩ I₂)

    RHS : ∀ {τ₁ τ₂} → ∃I⟨ τ₁ , τ₂ ⟩ → τ₁ ⋖♯ τ₂
    RHS (∃I ⊤) = ⊤Rτ
    RHS (∃I Any,⊤) = τR⊤
    RHS (∃I τ,Any) = ⋖♯Any
    RHS (∃I None,τ) = ⋖♯None
    RHS (∃I ⊤,None) = ⊤Rτ
    RHS (∃I ⟨𝔹⟩,⊤) = τR⊤
    RHS (∃I ⊤,⟨𝔹⟩) = ⊤Rτ
    RHS (∃I ⟨𝔹⟩) = ⟨𝔹⟩
    RHS (∃I (I₁ ⟨→⟩⊤ I₂)) = τR⊤
    RHS (∃I (I₁ ⊤⟨→⟩ I₂)) = ⊤Rτ
    RHS (∃I (I₁ ⟨→⟩ I₂)) = RHS (∃I I₁) ⟨→⟩ RHS (∃I I₂)

¬⊤∃ : ∀ {τ♯} → not[⊤] τ♯ → ∃ τ 𝑠𝑡 ¬ (ηᵗ τ ⊑ τ♯)
¬⊤∃ Any = ⟨∃ None , (λ ()) ⟩
¬⊤∃ None = ⟨∃ ⟨𝔹⟩ , (λ ()) ⟩
¬⊤∃ ⟨𝔹⟩ = ⟨∃ None , (λ ()) ⟩
¬⊤∃ [⟨→⟩] = ⟨∃ None , (λ ()) ⟩

-- complete[I] : ∀ {τ₁♯ τ₂♯ τ₁ᴵ♯ τ₂ᴵ♯}
--   → ⟨ τ₁ᴵ♯ , τ₂ᴵ♯ ⟩∈I⟨ τ₁♯ , τ₂♯ ⟩
--   → ∀ {τ₁ᴵ'♯ τ₂ᴵ'♯}
--   → (∀ {τ₁ τ₂} → τ₁ ∈γᵗ[ τ₁♯ ] → τ₂ ∈γᵗ[ τ₂♯ ] → τ₁ ⋖ τ₂ → ηᵗ τ₁ ≼ τ₁ᴵ'♯ ∧ ηᵗ τ₂ ≼ τ₂ᴵ'♯)
--   → τ₁ᴵ♯ ≼ τ₁ᴵ'♯ ∧ τ₂ᴵ♯ ≼ τ₂ᴵ'♯
-- complete[I] ⊤ {τ₁ᴵ'♯} {τ₂ᴵ'♯} P with dec[⊤] τ₁ᴵ'♯ | dec[⊤] τ₂ᴵ'♯
-- complete[I] ⊤ P | Inl ⊤ | Inl ⊤ = ⊤ , ⊤
-- complete[I] ⊤ P | _ | Inr ¬⊤ with ¬⊤∃ ¬⊤
-- … | ∃ τ ,, ¬≼ = exfalso (¬≼ (π₂ (P ⊤ ⊤ xRx)))
-- complete[I] ⊤ P | Inr ¬⊤ | _ with ¬⊤∃ ¬⊤
-- … | ∃ τ ,, ¬≼ = exfalso (¬≼ (π₁ (P ⊤ ⊤ xRx)))
-- complete[I] Any,⊤ P = P Any ⊤ Any
-- complete[I] τ,Any P = {!!}
-- complete[I] None,τ P = {!!}
-- complete[I] ⊤,None P = {!!}
-- complete[I] ⟨𝔹⟩,⊤ P = {!!}
-- complete[I] ⊤,⟨𝔹⟩ P = {!!}
-- complete[I] ⟨𝔹⟩ P = {!!}
-- complete[I] (I₁ ⟨→⟩⊤ I₂) P = {!!}
-- complete[I] (I₁ ⊤⟨→⟩ I₂) P = {!!}
-- complete[I] (I₁ ⟨→⟩ I₂) P = {!!} 

-- -- X : A → prop
-- 
-- -- ⨆ : (A → Set) → (A → Set)
-- -- ⨆ X x' = ∀ x'' → (∀ x → x ∈ X → x ≼ x'') → x' ≼ x''
-- -- lub X ≔ { x | 
-- 
-- -- ⨆(pure(η)*(↑P(γ(y)))) = {I(y)}
-- -- ⨆(pure(η)*(↑P{x | x ∈γ[ y ]}) = {I(y)}
-- -- ⨆(pure(η)*({x | x ∈γ[ y ] ∧ P(x)}) = {I(y)}
-- -- ⨆({η(x) | x ∈γ[ y ] ∧ P(x)}) = {I(y)}
-- -- {y' | ∀ y'', (∀ x, x ∈γ[ y ] → P(x) → η(x) ≼ y'') → y' ≼ y''} = {I(y)}
-- (∀ y'', (∀ x, x ∈γ[ y ] ∧ P(x) → η(x) ≼ y'') → y' ≼ y'') ↔ y' ≼ I(y)
-- 
-- 
-- ∀ y', (∀ x, x ∈γ[ y ] ∧ P(x) → η(x) ≼ y') → I(y) ≼ y'
-- 
-- 
-- (∀ x, x ∈γ[ y ] ∧ P(x) → η(x) ≼ y')
-- --------------------------------------------------------
-- y' ≼ I(y)
-- 
-- (∀ x, x ∈γ[ y ] ∧ P(x) → η(x) ≼ y')
-- ----------
-- I(y) ≼ y'
-- 
-- ⨆(X) = Y
-- ⇔
-- (∀ x'', (∀ x, x ∈ X → x ≼ x'') → x' ≼ x'') ↔ x' ≼ y
-- 
-- 
-- ⇒
-- (∀ x'', (∀ x, x ∈ X → x ≼ x'') → x' ≼ x'') → x' ≼ y
-- 
-- ⇐
-- x' ≼ y → ∀ x'', (∀ x, x ∈ X → x ≼ x'') → x' ≼ x''
-- ⇔
-- ∀ x'', (∀ x, x ∈ X → x ≼ x'') → y ≼ x''

-----------
-- Terms --
-----------

data context♯ : Set where
  [] : context♯
  _∷_ : type♯ → context♯ → context♯

data _⋳♯_ : type♯ → context♯ → Set where
  Zero : ∀ {Γ τ} → τ ⋳♯ (τ ∷ Γ)
  Succ : ∀ {Γ τ₁ τ₂} → τ₁ ⋳♯ Γ → τ₁ ⋳♯ (τ₂ ∷ Γ)

mutual
  data _⊢♯_ : context♯ → type♯ → Set where
    ⟨𝔹⟩ : ∀ {Γ} → 𝔹 → Γ ⊢♯ ⟨𝔹⟩
    ⟨if⟩_⟨then⟩_⟨else⟩_ : ∀ {Γ τ₂ τ₃}
      → Γ ⊢⦂♯ ⟨𝔹⟩
      → Γ ⊢⦂♯ τ₂
      → Γ ⊢⦂♯ τ₃
      → Γ ⊢♯ τ₂ ⟇♯ τ₃
    Var : ∀ {Γ τ}
      → τ ⋳♯ Γ
      → Γ ⊢♯ τ
    ⟨λ⟩ : ∀ {Γ τ₁ τ₂}
      → τ₁ ∷ Γ ⊢♯ τ₂
      → Γ ⊢♯ τ₁ ⟨→⟩ τ₂
    _⟨⋅⟩_ : ∀ {Γ τ₁ τ₂}
      → Γ ⊢⦂♯ τ₁ ⟨→⟩ τ₂
      → Γ ⊢⦂♯ τ₁
      → Γ ⊢♯ τ₂
    ⟪_⟫ : ∀ {Γ τ}
      → Γ ⊢⦂♯ τ
      → Γ ⊢♯ τ
  data _⊢⦂♯_ : context♯ → type♯ → Set where
    _⦂⦂_ : ∀ {Γ τ₁ τ₂}
      → Γ ⊢♯ τ₁
      → τ₁ ⋖♯ τ₂
      → Γ ⊢⦂♯ τ₂

--------------
-- Renaming --
--------------

data _⊲♯_ : context♯ → context♯ → Set where
  [] : ∀ {Γ} → [] ⊲♯ Γ 
  _∷_ : ∀ {Γ₁ Γ₂ τ} → τ ⋳♯ Γ₂ → Γ₁ ⊲♯ Γ₂ → τ ∷ Γ₁ ⊲♯ Γ₂

rename[⋳♯][_] : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊲♯ Γ₂ → τ ⋳♯ Γ₁ → τ ⋳♯ Γ₂
rename[⋳♯][ x ∷ φ ] Zero = x
rename[⋳♯][ x₂ ∷ φ ] (Succ x₁) = rename[⋳♯][ φ ] x₁

_⊚⸢⊲♯⸣_ : transitive _⊲♯_
φ₂ ⊚⸢⊲♯⸣ [] = []
φ₂ ⊚⸢⊲♯⸣ (x ∷ φ₁) = rename[⋳♯][ φ₂ ] x ∷ (φ₂ ⊚⸢⊲♯⸣ φ₁)

weaken[⊲♯] : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊲♯ Γ₂ → Γ₁ ⊲♯ τ ∷ Γ₂
weaken[⊲♯] [] = []
weaken[⊲♯] (x ∷ φ) = Succ x ∷ weaken[⊲♯] φ

lift[⊲♯] : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊲♯ Γ₂ → τ ∷ Γ₁ ⊲♯ τ ∷ Γ₂
lift[⊲♯] φ = Zero ∷ weaken[⊲♯] φ

xRx⸢⊲♯⸣ : reflexive _⊲♯_
xRx⸢⊲♯⸣ {[]} = []
xRx⸢⊲♯⸣ {τ ∷ Γ} = lift[⊲♯] xRx⸢⊲♯⸣

instance
  Reflexive[⊲♯] : Reflexive _⊲♯_
  Reflexive[⊲♯] = record { xRx = xRx⸢⊲♯⸣ }
  Transitive[⊲♯] : Transitive _⊲♯_
  Transitive[⊲♯] = record { _⊚_ = _⊚⸢⊲♯⸣_ }

intro[⊲♯] : ∀ {Γ τ} → Γ ⊲♯ τ ∷ Γ
intro[⊲♯] = weaken[⊲♯] xRx

swap[⊲♯] : ∀ {Γ τ₁ τ₂} → τ₁ ∷ (τ₂ ∷ Γ) ⊲♯ τ₂ ∷ (τ₁ ∷ Γ)
swap[⊲♯] = Succ Zero ∷ lift[⊲♯] intro[⊲♯]

mutual
  rename[⊢♯][_] : ∀ {τ Γ₁ Γ₂} → Γ₁ ⊲♯ Γ₂ → Γ₁ ⊢♯ τ → Γ₂ ⊢♯ τ
  rename[⊢♯][ φ ] (⟨𝔹⟩ b) = ⟨𝔹⟩ b
  rename[⊢♯][ φ ] (⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃) = ⟨if⟩ rename[⊢⦂♯][ φ ] e₁ ⟨then⟩ rename[⊢⦂♯][ φ ] e₂ ⟨else⟩ rename[⊢⦂♯][ φ ] e₃
  rename[⊢♯][ φ ] (Var x) = Var (rename[⋳♯][ φ ] x)
  rename[⊢♯][ φ ] (⟨λ⟩ e) = ⟨λ⟩ (rename[⊢♯][ lift[⊲♯] φ ] e)
  rename[⊢♯][ φ ] (e₁ ⟨⋅⟩ e₂) = rename[⊢⦂♯][ φ ] e₁ ⟨⋅⟩ rename[⊢⦂♯][ φ ] e₂
  rename[⊢♯][ φ ] (⟪ e ⟫) = ⟪ rename[⊢⦂♯][ φ ] e ⟫

  rename[⊢⦂♯][_] : ∀ {τ Γ₁ Γ₂} → Γ₁ ⊲♯ Γ₂ → Γ₁ ⊢⦂♯ τ → Γ₂ ⊢⦂♯ τ
  rename[⊢⦂♯][ φ ] (e ⦂⦂ ε) = rename[⊢♯][ φ ] e ⦂⦂ ε

---------
-- Cut --
---------

cut[⋳♯][_] : ∀ {Γ₁ Γ₂ τ₁ τ₂} → Γ₁ ⊲♯ τ₁ ∷ Γ₂ → τ₂ ⋳♯ Γ₁ → Γ₂ ⊢♯ τ₁ → Γ₂ ⊢♯ τ₂
cut[⋳♯][ Zero ∷ φ ] Zero e = e
cut[⋳♯][ Succ x ∷ φ ] Zero e = Var x
cut[⋳♯][ x₂ ∷ φ ] (Succ x₁) e = cut[⋳♯][ φ ] x₁ e

mutual
  cut[⊢♯][_] : ∀ {Γ₁ Γ₂ τ₁ τ₂} → Γ₁ ⊲♯ τ₁ ∷ Γ₂ → Γ₁ ⊢♯ τ₂ → Γ₂ ⊢♯ τ₁ → Γ₂ ⊢♯ τ₂
  cut[⊢♯][ φ ] (⟨𝔹⟩ b) e₂ = ⟨𝔹⟩ b
  cut[⊢♯][ φ ] (⟨if⟩ e₁₁ ⟨then⟩ e₂₁ ⟨else⟩ e₃₁) e₂ = ⟨if⟩ cut[⊢⦂♯][ φ ] e₁₁ e₂ ⟨then⟩ cut[⊢⦂♯][ φ ] e₂₁ e₂ ⟨else⟩ cut[⊢⦂♯][ φ ] e₃₁ e₂
  cut[⊢♯][ φ ] (Var x) e₂ = cut[⋳♯][ φ ] x e₂
  cut[⊢♯][ φ ] (⟨λ⟩ e₁) e₂ = ⟨λ⟩ (cut[⊢♯][ swap[⊲♯] ⊚ lift[⊲♯] φ ] e₁ (rename[⊢♯][ intro[⊲♯] ] e₂))
  cut[⊢♯][ φ ] (e₁₁ ⟨⋅⟩ e₂₁) e₂ = cut[⊢⦂♯][ φ ] e₁₁ e₂ ⟨⋅⟩ cut[⊢⦂♯][ φ ] e₂₁ e₂
  cut[⊢♯][ φ ] (⟪ e₁ ⟫) e₂ = ⟪ cut[⊢⦂♯][ φ ] e₁ e₂ ⟫

  cut[⊢⦂♯][_] : ∀ {Γ₁ Γ₂ τ₁ τ₂} → Γ₁ ⊲♯ τ₁ ∷ Γ₂ → Γ₁ ⊢⦂♯ τ₂ → Γ₂ ⊢♯ τ₁ → Γ₂ ⊢⦂♯ τ₂
  cut[⊢⦂♯][ φ ] (e₁ ⦂⦂ ε) e₂ = cut[⊢♯][ φ ] e₁ e₂ ⦂⦂ ε

cut[⊢♯] : ∀ {Γ τ₁ τ₂} → τ₁ ∷ Γ ⊢♯ τ₂ → Γ ⊢♯ τ₁ → Γ ⊢♯ τ₂
cut[⊢♯] = cut[⊢♯][ xRx ]

---------------
-- Reduction --
---------------

data _↦♯_ {Γ} : ∀ {τ} → relation 0ᴸ (Γ ⊢♯ τ) where
  If/T :
    ∀ {τ₂₁ τ₂₂ τ₃₁ τ₃₂} {e₂ : Γ ⊢♯ τ₂₁} {ε₂ : τ₂₁ ⋖♯ τ₂₂} {e₃ : Γ ⊢♯ τ₃₁} {ε₃ : τ₃₁ ⋖♯ τ₃₂}
    → (⟨if⟩ ⟨𝔹⟩ True ⦂⦂ ⟨𝔹⟩ ⟨then⟩ e₂ ⦂⦂ ε₂ ⟨else⟩ e₃ ⦂⦂ ε₃) ↦♯ ⟪ e₂ ⦂⦂ weaken[⋖♯]/L[ τ₃₂ ] ε₂ ⟫
  If/F :
    ∀ {τ₂₁ τ₂₂ τ₃₁ τ₃₂} {e₂ : Γ ⊢♯ τ₂₁} {ε₂ : τ₂₁ ⋖♯ τ₂₂} {e₃ : Γ ⊢♯ τ₃₁} {ε₃ : τ₃₁ ⋖♯ τ₃₂}
    → (⟨if⟩ ⟨𝔹⟩ False ⦂⦂ ⟨𝔹⟩ ⟨then⟩ e₂ ⦂⦂ ε₂ ⟨else⟩ e₃ ⦂⦂ ε₃) ↦♯ ⟪ e₃ ⦂⦂ weaken[⋖♯]/R[ τ₂₂ ] ε₃ ⟫
--   App :
--     ∀ {τ₁₁ τ₂₁ τ₁₂ τ₂₂ τ₂} {e₁ : (τ₁₁ ∷ Γ) ⊢♯ τ₂₁} {ε₁ : τ₁₂ ⋖♯ τ₁₁} {ε₂ : τ₂₁ ⋖♯ τ₂₂} {e₂ : Γ ⊢♯ τ₂} {ε₃ : τ₂ ⋖♯ τ₁₂}
--     → (⟨λ⟩ e₁ ⦂⦂ (ε₁ ⟨→⟩ ε₂) ⟨⋅⟩ e₂ ⦂⦂ ε₃) ↦♯ ⟪ cut[⊢♯] e₁ ⟪ e₂ ⦂⦂ {!!} ⟫ ⦂⦂ ε₂ ⟫

mutual
  data _⇰♯_ {Γ} : ∀ {τ} → relation 0ᴸ (Γ ⊢♯ τ) where
    Axiom :
      ∀ {τ} {e e' : Γ ⊢♯ τ}
      → e ↦♯ e'
      → e ⇰♯ e'
    If/e₁ :
      ∀ {τ₂ τ₃} {e₁ e₁' : Γ ⊢⦂♯ ⟨𝔹⟩} {e₂ : Γ ⊢⦂♯ τ₂} {e₃ : Γ ⊢⦂♯ τ₃}
      → e₁ ⇰⦂♯ e₁'
      → ⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃ ⇰♯ ⟨if⟩ e₁' ⟨then⟩ e₂ ⟨else⟩ e₃
    If/e₂ :
      ∀ {τ₂ τ₃} {e₁ : Γ ⊢⦂♯ ⟨𝔹⟩} {e₂ e₂' : Γ ⊢⦂♯ τ₂} {e₃ : Γ ⊢⦂♯ τ₃}
      → e₂ ⇰⦂♯ e₂'
      → ⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃ ⇰♯ ⟨if⟩ e₁ ⟨then⟩ e₂' ⟨else⟩ e₃
    If/e₃ :
      ∀ {τ₂ τ₃} {e₁ : Γ ⊢⦂♯ ⟨𝔹⟩} {e₂ : Γ ⊢⦂♯ τ₂} {e₃ e₃' : Γ ⊢⦂♯ τ₃}
      → e₃ ⇰⦂♯ e₃'
      → ⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃ ⇰♯ ⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃'
    Lam :
      ∀ {τ₁ τ₂} {e e' : (τ₁ ∷ Γ) ⊢♯ τ₂}
      → e ⇰♯ e'
      → ⟨λ⟩ e ⇰♯ ⟨λ⟩ e'
    App/e₁ :
      ∀ {τ₁ τ₂} {e₁ e₁' : Γ ⊢⦂♯ (τ₁ ⟨→⟩ τ₂)} {e₂ : Γ ⊢⦂♯ τ₁}
      → e₁ ⇰⦂♯ e₁'
      → e₁ ⟨⋅⟩ e₂ ⇰♯ e₁' ⟨⋅⟩ e₂
    App/e₂ :
      ∀ {τ₁ τ₂} {e₁ : Γ ⊢⦂♯ (τ₁ ⟨→⟩ τ₂)} {e₂ e₂' : Γ ⊢⦂♯ τ₁}
      → e₂ ⇰⦂♯ e₂'
      → e₁ ⟨⋅⟩ e₂ ⇰♯ e₁ ⟨⋅⟩ e₂'
    Cast : ∀ {τ} {e e' : Γ ⊢⦂♯ τ}
      → e ⇰⦂♯ e'
      → ⟪ e ⟫ ⇰♯ ⟪ e' ⟫

  data _⇰⦂♯_ {Γ} : ∀ {τ} → relation 0ᴸ (Γ ⊢⦂♯ τ) where
    Cast/e :
      ∀ {τ₁ τ₂} {e e' : Γ ⊢♯ τ₁} {ε : τ₁ ⋖♯ τ₂}
      → e ⇰♯ e'
      → e ⦂⦂ ε ⇰⦂♯ e' ⦂⦂ ε
--     Cast/ε : ∀ {τ₁ τ₂ τ₃} {e : Γ ⊢♯ τ₁} {ε₁ : τ₁ ⋖♯ τ₂} {ε₂ : τ₂ ⋖♯ τ₃}
--       → ⟪ e ⦂⦂ ε₁ ⟫ ⦂⦂ ε₂ ⇰⦂♯ e ⦂⦂ {!!}
