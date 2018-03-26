module AGT.Precise where

open import Prelude

infix  14 _⊲_
infix  14 _⋖_
infix  14 _⋳_
infix  14 _⊢_
infix  14 _⊢⦂_
infix  14 _↦_
infix  14 _⇰_
infix  14 _⇰⦂_
infix  14 _⊢_⇓_
infix  14 _⊢_⇓⦂_

infixr 15 _⟨→⟩_
infixr 16 ⟨if⟩_⟨then⟩_⟨else⟩_
infixl 17 _⟨⋅⟩_
infixl 18 _⦂⦂_

infixr 22 _⟇_
infixr 24 _⟑_

infixr 30 _⊚⸢⋖⸣_

infixr 40 _∷_

-------------------
-- Type Language --
-------------------

data type : Set where
  Any : type
  None : type
  ⟨𝔹⟩ : type
  _⟨→⟩_ : type → type → type

instance
  PreOrder[type] : Precision 0ᴸ type
  PreOrder[type] = mk[Precision] _≡_

---------------
-- Subtyping --
---------------

data _⋖_ : type → type → Set where
  Any : ∀ {τ} → τ ⋖ Any
  None : ∀ {τ} → None ⋖ τ
  ⟨𝔹⟩ : ⟨𝔹⟩ ⋖ ⟨𝔹⟩
  _⟨→⟩_ : ∀ {τ₁₁ τ₂₁ τ₁₂ τ₂₂}
    → τ₂₁ ⋖ τ₁₁
    → τ₁₂ ⋖ τ₂₂
    → τ₁₁ ⟨→⟩ τ₁₂ ⋖ τ₂₁ ⟨→⟩ τ₂₂

xRx⸢⋖⸣ : ∀ {τ} → τ ⋖ τ
xRx⸢⋖⸣ {Any} = Any
xRx⸢⋖⸣ {None} = None
xRx⸢⋖⸣ {⟨𝔹⟩} = ⟨𝔹⟩
xRx⸢⋖⸣ {τ₁ ⟨→⟩ τ₂} = xRx⸢⋖⸣ ⟨→⟩ xRx⸢⋖⸣

_⊚⸢⋖⸣_ : ∀ {τ₁ τ₂ τ₃} → τ₂ ⋖ τ₃ → τ₁ ⋖ τ₂ → τ₁ ⋖ τ₃
Any ⊚⸢⋖⸣ _ = Any
_ ⊚⸢⋖⸣ None = None
⟨𝔹⟩ ⊚⸢⋖⸣ ⟨𝔹⟩ = ⟨𝔹⟩
(τ₁₁ ⟨→⟩ τ₂₁) ⊚⸢⋖⸣ (τ₁₂ ⟨→⟩ τ₂₂) = τ₁₂ ⊚⸢⋖⸣ τ₁₁ ⟨→⟩ τ₂₁ ⊚⸢⋖⸣ τ₂₂

instance
  Reflexive[⋖] : Reflexive _⋖_
  Reflexive[⋖] = record { xRx = xRx⸢⋖⸣ }
  Transitive[⋖] : Transitive _⋖_
  Transitive[⋖] = record { _⊚_ = _⊚⸢⋖⸣_ }

---------------------------
-- Subtype Join and Meet --
---------------------------

mutual
  _⟇_ : type → type → type
  Any ⟇ _ = Any
  _ ⟇ Any = Any
  None ⟇ τ = τ
  τ ⟇ None = τ
  ⟨𝔹⟩ ⟇ ⟨𝔹⟩ = ⟨𝔹⟩
  (τ₁₁ ⟨→⟩ τ₂₁) ⟇ (τ₁₂ ⟨→⟩ τ₂₂) = τ₁₁ ⟑ τ₁₂ ⟨→⟩ τ₂₁ ⟇ τ₂₂
  ⟨𝔹⟩ ⟇ (_ ⟨→⟩ _) = Any
  (_ ⟨→⟩ _) ⟇ ⟨𝔹⟩ = Any

  _⟑_ : type → type → type
  Any ⟑ τ = τ
  τ ⟑ Any = τ
  None ⟑ _ = None
  _ ⟑ None = None
  ⟨𝔹⟩ ⟑ ⟨𝔹⟩ = ⟨𝔹⟩
  (τ₁₁ ⟨→⟩ τ₂₁) ⟑ (τ₁₂ ⟨→⟩ τ₂₂) = τ₁₁ ⟇ τ₁₂ ⟨→⟩ τ₂₁ ⟑ τ₂₂
  ⟨𝔹⟩ ⟑ (y ⟨→⟩ y₁) = None
  (x ⟨→⟩ x₁) ⟑ ⟨𝔹⟩ = None

unit[⟇] : ∀ τ → None ⟇ τ ≡ τ ∧ τ ⟇ None ≡ τ
unit[⟇] Any = ⟨ ↯ , ↯ ⟩
unit[⟇] None = ⟨ ↯ , ↯ ⟩
unit[⟇] ⟨𝔹⟩ = ⟨ ↯ , ↯ ⟩
unit[⟇] (_ ⟨→⟩ _) = ⟨ ↯ , ↯ ⟩

zero[⟇] : ∀ τ → Any ⟇ τ ≡ Any ∧ τ ⟇ Any ≡ Any
zero[⟇] Any = ⟨ ↯ , ↯ ⟩
zero[⟇] None = ⟨ ↯ , ↯ ⟩
zero[⟇] ⟨𝔹⟩ = ⟨ ↯ , ↯ ⟩
zero[⟇] (_ ⟨→⟩ _) = ⟨ ↯ , ↯ ⟩

unit[⟑] : ∀ τ → Any ⟑ τ ≡ τ ∧ τ ⟑ Any ≡ τ
unit[⟑] Any = ⟨ ↯ , ↯ ⟩
unit[⟑] None = ⟨ ↯ , ↯ ⟩
unit[⟑] ⟨𝔹⟩ = ⟨ ↯ , ↯ ⟩
unit[⟑] (_ ⟨→⟩ _) = ⟨ ↯ , ↯ ⟩

zero[⟑] : ∀ τ → None ⟑ τ ≡ None ∧ τ ⟑ None ≡ None
zero[⟑] Any = ⟨ ↯ , ↯ ⟩
zero[⟑] None = ⟨ ↯ , ↯ ⟩
zero[⟑] ⟨𝔹⟩ = ⟨ ↯ , ↯ ⟩
zero[⟑] (_ ⟨→⟩ _) = ⟨ ↯ , ↯ ⟩

mutual
  ⋖⟇ : ∀ {τ₁ τ₂} → τ₁ ⋖ τ₁ ⟇ τ₂ ∧ τ₂ ⋖ τ₁ ⟇ τ₂
  ⋖⟇ {Any} {_} = ⟨ Any , Any ⟩
  ⋖⟇ {τ₁} {Any} rewrite π₂ (zero[⟇] τ₁) = ⟨ Any , Any ⟩
  ⋖⟇ {None} {τ₂} rewrite π₁ (unit[⟇] τ₂) = ⟨ None , xRx ⟩
  ⋖⟇ {τ₁} {None} rewrite π₂ (unit[⟇] τ₁) = ⟨ xRx , None ⟩
  ⋖⟇ {⟨𝔹⟩} {⟨𝔹⟩} = ⟨ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩
  ⋖⟇ {τ₁₁ ⟨→⟩ τ₂₁} {τ₁₂ ⟨→⟩ τ₂₂} with ⋖⟑ {τ₁₁} {τ₁₂} | ⋖⟇ {τ₂₁} {τ₂₂}
  ... | ⟨ <⟑₁ , <⟑₂ ⟩ | ⟨ <⟇₁ , <⟇₂ ⟩ = ⟨ <⟑₁ ⟨→⟩ <⟇₁ , <⟑₂ ⟨→⟩ <⟇₂ ⟩
  ⋖⟇ {⟨𝔹⟩} {_ ⟨→⟩ _} = ⟨ Any , Any ⟩
  ⋖⟇ {_ ⟨→⟩ _} {⟨𝔹⟩} = ⟨ Any , Any ⟩

  ⋖⟑ : ∀ {τ₁ τ₂} → τ₁ ⟑ τ₂ ⋖ τ₁ ∧ τ₁ ⟑ τ₂ ⋖ τ₂
  ⋖⟑ {Any} {_} = ⟨ Any , xRx ⟩
  ⋖⟑ {τ₁} {Any} rewrite π₂ (unit[⟑] τ₁) = ⟨ xRx , Any ⟩
  ⋖⟑ {None} {τ₂} rewrite π₁ (zero[⟑] τ₂) = ⟨ None , None ⟩
  ⋖⟑ {τ₁} {None} rewrite π₂ (zero[⟑] τ₁) = ⟨ None , None ⟩
  ⋖⟑ {⟨𝔹⟩} {⟨𝔹⟩} = ⟨ ⟨𝔹⟩ , ⟨𝔹⟩ ⟩
  ⋖⟑ {τ₁₁ ⟨→⟩ τ₂₁} {τ₁₂ ⟨→⟩ τ₂₂} with ⋖⟇ {τ₁₁} {τ₁₂} | ⋖⟑ {τ₂₁} {τ₂₂}
  ... | ⟨ <⟇₁ , <⟇₂ ⟩ | ⟨ <⟑₁ , <⟑₂ ⟩ = ⟨ <⟇₁ ⟨→⟩ <⟑₁ , <⟇₂ ⟨→⟩ <⟑₂ ⟩
  ⋖⟑ {⟨𝔹⟩} {_ ⟨→⟩ _} = ⟨ None , None ⟩
  ⋖⟑ {_ ⟨→⟩ _} {⟨𝔹⟩} = ⟨ None , None ⟩

⋖⟇/L : ∀ {τ₁} τ₂ → τ₁ ⋖ τ₁ ⟇ τ₂
⋖⟇/L τ₂ = π₁ (⋖⟇ {_} {τ₂})

⋖⟇/R : ∀ τ₁ {τ₂} → τ₂ ⋖ τ₁ ⟇ τ₂
⋖⟇/R τ₁ = π₂ (⋖⟇ {τ₁})

⋖⟑/L : ∀ {τ₁} τ₂ → τ₁ ⟑ τ₂ ⋖ τ₁
⋖⟑/L τ₂ = π₁ (⋖⟑ {_} {τ₂})

⋖⟑/R : ∀ τ₁ {τ₂} → τ₁ ⟑ τ₂ ⋖ τ₂
⋖⟑/R τ₁ = π₂ (⋖⟑ {τ₁})

-------------------
-- Term Language --
-------------------

data context : Set where
  [] : context
  _∷_ : type → context → context

data _⋳_ : type → context → Set where
  Zero : ∀ {Γ τ} → τ ⋳ τ ∷ Γ
  Succ : ∀ {Γ τ₁ τ₂} → τ₁ ⋳ Γ → τ₁ ⋳ τ₂ ∷ Γ

mutual
  data _⊢_ : context → type → Set where
    ⟨𝔹⟩ : ∀ {Γ}
      → 𝔹 → Γ ⊢ ⟨𝔹⟩
    ⟨if⟩_⟨then⟩_⟨else⟩_ : ∀ {Γ τ₂ τ₃}
      → Γ ⊢⦂ ⟨𝔹⟩
      → Γ ⊢⦂ τ₂
      → Γ ⊢⦂ τ₃
      → Γ ⊢ τ₂ ⟇ τ₃
    Var : ∀ {Γ τ}
      → τ ⋳ Γ
      → Γ ⊢ τ
    ⟨λ⟩ : ∀ {Γ τ₁ τ₂}
      → τ₁ ∷ Γ ⊢ τ₂
      → Γ ⊢ τ₁ ⟨→⟩ τ₂
    _⟨⋅⟩_ : ∀ {Γ τ₁ τ₂}
      → Γ ⊢⦂ τ₁ ⟨→⟩ τ₂
      → Γ ⊢⦂ τ₁
      → Γ ⊢ τ₂
    ⟪_⟫ : ∀ {Γ τ}
      → Γ ⊢⦂ τ
      → Γ ⊢ τ

  data _⊢⦂_ : context → type → Set where
    _⦂⦂_ : ∀ {Γ τ₁ τ₂}
      → Γ ⊢ τ₁
      → τ₁ ⋖ τ₂
      → Γ ⊢⦂ τ₂

--------------
-- Renaming --
--------------

data _⊲_ : context → context → Set where
  [] : ∀ {Γ} → [] ⊲ Γ
  _∷_ : ∀ {Γ₁ Γ₂ τ} → τ ⋳ Γ₂ → Γ₁ ⊲ Γ₂ → τ ∷ Γ₁ ⊲ Γ₂

rename[⋳] : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊲ Γ₂ → τ ⋳ Γ₁ → τ ⋳ Γ₂
rename[⋳] (x ∷ φ) Zero = x
rename[⋳] (x₂ ∷ φ) (Succ x₁) = rename[⋳] φ x₁

_⊚⸢⊲⸣_ : ∀ {Γ₁ Γ₂ Γ₃} → Γ₂ ⊲ Γ₃ → Γ₁ ⊲ Γ₂ → Γ₁ ⊲ Γ₃
φ ⊚⸢⊲⸣ [] = []
φ₂ ⊚⸢⊲⸣ (x ∷ φ₁) = rename[⋳] φ₂ x ∷ (φ₂ ⊚⸢⊲⸣ φ₁)

weaken[⊲] : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊲ Γ₂ → Γ₁ ⊲ τ ∷ Γ₂
weaken[⊲] [] = []
weaken[⊲] (x ∷ φ) = Succ x ∷ weaken[⊲] φ

lift[⊲] : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊲ Γ₂ → τ ∷ Γ₁ ⊲ τ ∷ Γ₂
lift[⊲] φ = Zero ∷ weaken[⊲] φ

xRx⸢⊲⸣ : ∀ {Γ} → Γ ⊲ Γ
xRx⸢⊲⸣ {[]} = []
xRx⸢⊲⸣ {x ∷ Γ} = lift[⊲] xRx⸢⊲⸣

instance
  Reflexive[⊴ʳ] : Reflexive _⊲_
  Reflexive[⊴ʳ] = record { xRx = xRx⸢⊲⸣ }
  Transitive[⊴ʳ] : Transitive _⊲_
  Transitive[⊴ʳ] = record { _⊚_ = _⊚⸢⊲⸣_ }

intro[⊲] : ∀ {Γ τ} → Γ ⊲ τ ∷ Γ
intro[⊲] = weaken[⊲] xRx

swap[⊲] : ∀ {Γ τ₁ τ₂} → τ₁ ∷ τ₂ ∷ Γ ⊲ τ₂ ∷ τ₁ ∷ Γ
swap[⊲] = Succ Zero ∷ lift[⊲] intro[⊲]

mutual
  rename[⊢][_] : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊲ Γ₂ → Γ₁ ⊢ τ → Γ₂ ⊢ τ
  rename[⊢][ φ ] (⟨𝔹⟩ b) = ⟨𝔹⟩ b
  rename[⊢][ φ ] (⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃) = ⟨if⟩ rename[⊢⦂][ φ ] e₁ ⟨then⟩ rename[⊢⦂][ φ ] e₂ ⟨else⟩ rename[⊢⦂][ φ ] e₃
  rename[⊢][ φ ] (Var x) = Var (rename[⋳] φ x)
  rename[⊢][ φ ] (⟨λ⟩ e) = ⟨λ⟩ (rename[⊢][ lift[⊲] φ ] e)
  rename[⊢][ φ ] (e₁ ⟨⋅⟩ e₂) = rename[⊢⦂][ φ ] e₁ ⟨⋅⟩ rename[⊢⦂][ φ ] e₂
  rename[⊢][ φ ] ⟪ e ⟫ = ⟪ rename[⊢⦂][ φ ] e ⟫
  
  rename[⊢⦂][_] : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊲ Γ₂ → Γ₁ ⊢⦂ τ → Γ₂ ⊢⦂ τ
  rename[⊢⦂][ φ ] (e ⦂⦂ ε) = rename[⊢][ φ ] e ⦂⦂ ε

---------
-- Cut --
---------

cut[⋳][_] : ∀ {Γ₁ Γ₂ τ₁ τ₂} → Γ₁ ⊲ τ₁ ∷ Γ₂ → τ₂ ⋳ Γ₁ → Γ₂ ⊢ τ₁ → Γ₂ ⊢ τ₂
cut[⋳][ Zero ∷ φ ] Zero e = e
cut[⋳][ Succ x ∷ φ ] Zero e = Var x
cut[⋳][ x₂ ∷ φ ] (Succ x₁) e = cut[⋳][ φ ] x₁ e

mutual
  cut[⊢][_] : ∀ {Γ₁ Γ₂ τ₁ τ₂} → Γ₁ ⊲ τ₁ ∷ Γ₂ → Γ₁ ⊢ τ₂ → Γ₂ ⊢ τ₁ → Γ₂ ⊢ τ₂
  cut[⊢][ φ ] (⟨𝔹⟩ b) e = ⟨𝔹⟩ b
  cut[⊢][ φ ] (⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃) e = ⟨if⟩ cut[⊢⦂][ φ ] e₁ e ⟨then⟩ cut[⊢⦂][ φ ] e₂ e ⟨else⟩ cut[⊢⦂][ φ ] e₃ e
  cut[⊢][ φ ] (Var x) e = cut[⋳][ φ ] x e
  cut[⊢][ φ ] (⟨λ⟩ e₁) e = ⟨λ⟩ (cut[⊢][ swap[⊲] ⊚ lift[⊲] φ ] e₁ (rename[⊢][ intro[⊲] ] e))
  cut[⊢][ φ ] (e₁ ⟨⋅⟩ e₂) e = cut[⊢⦂][ φ ] e₁ e ⟨⋅⟩ cut[⊢⦂][ φ ] e₂ e
  cut[⊢][ φ ] ⟪ e₁ ⟫ e = ⟪ cut[⊢⦂][ φ ] e₁ e ⟫

  cut[⊢⦂][_] : ∀ {Γ₁ Γ₂ τ₁ τ₂} → Γ₁ ⊲ τ₁ ∷ Γ₂ → Γ₁ ⊢⦂ τ₂ → Γ₂ ⊢ τ₁ → Γ₂ ⊢⦂ τ₂
  cut[⊢⦂][ φ ] (e₁ ⦂⦂ ε) e = cut[⊢][ φ ] e₁ e ⦂⦂ ε

cut[⊢] : ∀ {Γ τ₁ τ₂} → τ₁ ∷ Γ ⊢ τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂
cut[⊢] = cut[⊢][ xRx ]

---------------
-- Reduction --
---------------

data _↦_ {Γ} : ∀ {τ} → relation 0ᴸ (Γ ⊢ τ) where
  If/T : ∀ {τ₂₁ τ₂₂ τ₃₁ τ₃₂} {e₂ : Γ ⊢ τ₂₁} {ε₂ : τ₂₁ ⋖ τ₂₂} {e₃ : Γ ⊢ τ₃₁} {ε₃ : τ₃₁ ⋖ τ₃₂}
    → ⟨if⟩ ⟨𝔹⟩ True ⦂⦂ ⟨𝔹⟩ ⟨then⟩ e₂ ⦂⦂ ε₂ ⟨else⟩ e₃ ⦂⦂ ε₃ ↦ ⟪ e₂ ⦂⦂ ⋖⟇/L τ₃₂ ⊚ ε₂ ⟫
  If/F : ∀ {τ₂₁ τ₂₂ τ₃₁ τ₃₂} {e₂ : Γ ⊢ τ₂₁} {ε₂ : τ₂₁ ⋖ τ₂₂} {e₃ : Γ ⊢ τ₃₁} {ε₃ : τ₃₁ ⋖ τ₃₂}
    → ⟨if⟩ ⟨𝔹⟩ False ⦂⦂ ⟨𝔹⟩ ⟨then⟩ e₂ ⦂⦂ ε₂ ⟨else⟩ e₃ ⦂⦂ ε₃ ↦ ⟪ e₃ ⦂⦂ ⋖⟇/R τ₂₂ ⊚ ε₃ ⟫
  App : ∀ {τ₁₁ τ₁₂ τ₁₃ τ₂₁ τ₂₂} {e₁ : τ₁₂ ∷ Γ ⊢ τ₂₁} {ε₁₁ : τ₁₁ ⋖ τ₁₂} {ε₂₁ : τ₂₁ ⋖ τ₂₂} {e₂ : Γ ⊢ τ₁₃} {ε₂ : τ₁₃ ⋖ τ₁₁}
    → ⟨λ⟩ e₁ ⦂⦂ (ε₁₁ ⟨→⟩ ε₂₁) ⟨⋅⟩ e₂ ⦂⦂ ε₂ ↦ ⟪ cut[⊢] e₁ ⟪ e₂ ⦂⦂ ε₁₁ ⊚ ε₂ ⟫ ⦂⦂ ε₂₁ ⟫

mutual
  data _⇰_ {Γ} : ∀ {τ} → relation 0ᴸ (Γ ⊢ τ) where
    Axiom : ∀ {τ} {e e' : Γ ⊢ τ}
      → e ↦ e'
      → e ⇰ e'
    If/e₁ : ∀ {τ₂ τ₃} {e₁ e₁' : Γ ⊢⦂ ⟨𝔹⟩} {e₂ : Γ ⊢⦂ τ₂} {e₃ : Γ ⊢⦂ τ₃}
      → e₁ ⇰⦂ e₁'
      → ⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃ ⇰ ⟨if⟩ e₁' ⟨then⟩ e₂ ⟨else⟩ e₃
    If/e₂ : ∀ {τ₂ τ₃} {e₁ : Γ ⊢⦂ ⟨𝔹⟩} {e₂ e₂' : Γ ⊢⦂ τ₂} {e₃ : Γ ⊢⦂ τ₃}
      → e₂ ⇰⦂ e₂'
      → ⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃ ⇰ ⟨if⟩ e₁ ⟨then⟩ e₂' ⟨else⟩ e₃
    If/e₃ : ∀ {τ₂ τ₃} {e₁ : Γ ⊢⦂ ⟨𝔹⟩} {e₂ : Γ ⊢⦂ τ₂} {e₃ e₃' : Γ ⊢⦂ τ₃}
      → e₃ ⇰⦂ e₃'
      → ⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃ ⇰ ⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃'
    Lam : ∀ {τ₁ τ₂} {e e' : τ₁ ∷ Γ ⊢ τ₂}
      → e ⇰ e'
      → ⟨λ⟩ e ⇰ ⟨λ⟩ e'
    App/e₁ : ∀ {τ₁ τ₂} {e₁ e₁' : Γ ⊢⦂ τ₁ ⟨→⟩ τ₂} {e₂ : Γ ⊢⦂ τ₁}
      → e₁ ⇰⦂ e₁'
      → e₁ ⟨⋅⟩ e₂ ⇰ e₁' ⟨⋅⟩ e₂
    App/e₂ : ∀ {τ₁ τ₂} {e₁ : Γ ⊢⦂ τ₁ ⟨→⟩ τ₂} {e₂ e₂' : Γ ⊢⦂ τ₁}
      → e₂ ⇰⦂ e₂'
      → e₁ ⟨⋅⟩ e₂ ⇰ e₁ ⟨⋅⟩ e₂'
    Cast : ∀ {τ} {e e' : Γ ⊢⦂ τ}
      → e ⇰⦂ e'
      → ⟪ e ⟫ ⇰ ⟪ e' ⟫

  data _⇰⦂_ {Γ} : ∀ {τ} → relation 0ᴸ (Γ ⊢⦂ τ) where
    Cast/e : ∀ {τ₁ τ₂} {e e' : Γ ⊢ τ₁} {ε : τ₁ ⋖ τ₂}
      → e ⇰ e'
      → e ⦂⦂ ε ⇰⦂ e' ⦂⦂ ε
    Cast/ε : ∀ {τ₁ τ₂ τ₃} {e : Γ ⊢ τ₁} {ε₁ : τ₁ ⋖ τ₂} {ε₂ : τ₂ ⋖ τ₃}
      → ⟪ e ⦂⦂ ε₁ ⟫ ⦂⦂ ε₂ ⇰⦂ e ⦂⦂ ε₂ ⊚ ε₁

mutual
  data is-val : ∀ {Γ τ} → Γ ⊢ τ → Set where
    ⟨𝔹⟩ : ∀ {Γ} b → is-val (⟨𝔹⟩ b 𝑎𝑡 Γ ⊢ ⟨𝔹⟩)
    ⟨λ⟩ : ∀ {Γ τ₁ τ₂} (e : τ₁ ∷ Γ ⊢ τ₂) → is-val (⟨λ⟩ e)
  data is-val<> : ∀ {Γ τ} → Γ ⊢ τ → Set where
    Val : ∀ {Γ τ} {e : Γ ⊢ τ} → is-val e → is-val<> e
    Val<> : ∀ {Γ τ} {e : Γ ⊢⦂ τ} → is-val⦂ e → is-val<> ⟪ e ⟫
  data is-val⦂ : ∀ {Γ τ} → Γ ⊢⦂ τ → Set where
    Val⦂ : ∀ {Γ τ₁ τ₂} {e : Γ ⊢ τ₁} {ε : τ₁ ⋖ τ₂} → is-val e → is-val⦂ (e ⦂⦂ ε)


----------------
-- Metatheory --
----------------

mutual
  progress : ∀ {τ} (e : [] ⊢ τ) → is-val e ∨ (∀ {τ'} (ε : τ ⋖ τ') → ∃ e' 𝑠𝑡 e ⦂⦂ ε ⇰⦂ e')
  progress (⟨𝔹⟩ b) = Inl (⟨𝔹⟩ b)
  progress (⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃) with progress⦂ e₁
  progress (⟨if⟩ .(⟨λ⟩ e₁) ⦂⦂ () ⟨then⟩ e₂ ⟨else⟩ e₃) | Inl (Val⦂ (⟨λ⟩ e₁))
  progress (⟨if⟩ .(⟨𝔹⟩ True) ⦂⦂ ⟨𝔹⟩ ⟨then⟩ e₂ ⦂⦂ ε₂ ⟨else⟩ _⦂⦂_ {τ₂ = τ₃} e₃ ε₃) | Inl (Val⦂ (⟨𝔹⟩ True)) = Inr (λ ε' → ⟨∃ ⟪ e₂ ⦂⦂ ⋖⟇/L τ₃ ⊚ ε₂ ⟫ ⦂⦂ ε' , Cast/e (Axiom If/T) ⟩)
  progress (⟨if⟩ .(⟨𝔹⟩ False) ⦂⦂ ⟨𝔹⟩ ⟨then⟩ _⦂⦂_ {τ₂ = τ₂} e₂ ε₂ ⟨else⟩ e₃ ⦂⦂ ε₃) | Inl (Val⦂ (⟨𝔹⟩ False)) = Inr (λ ε' → ⟨∃ ⟪ e₃ ⦂⦂ ⋖⟇/R τ₂ ⊚ ε₃ ⟫ ⦂⦂ ε' , Cast/e (Axiom If/F) ⟩)
  progress (⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃) | Inr ⟨∃ e₁' , ⇰₁ ⟩ = Inr (λ ε → ⟨∃ (⟨if⟩ e₁' ⟨then⟩ e₂ ⟨else⟩ e₃) ⦂⦂ ε , Cast/e (If/e₁ ⇰₁) ⟩)
  progress (Var ())
  progress (⟨λ⟩ e) = Inl (⟨λ⟩ e)
  progress (e₁ ⟨⋅⟩ e₂) with progress⦂ e₁
  progress ((.(⟨𝔹⟩ b) ⦂⦂ ()) ⟨⋅⟩ e₂) | Inl (Val⦂ (⟨𝔹⟩ b))
  progress ((.(⟨λ⟩ e₁) ⦂⦂ (ε₁₁ ⟨→⟩ ε₂₁)) ⟨⋅⟩ (e₂ ⦂⦂ ε₂)) | Inl (Val⦂ (⟨λ⟩ e₁)) = Inr (λ ε' → ⟨∃ ⟪ cut[⊢] e₁ ⟪ e₂ ⦂⦂ ε₁₁ ⊚ ε₂ ⟫ ⦂⦂ ε₂₁ ⟫ ⦂⦂ ε' , Cast/e (Axiom App) ⟩)
  progress (e₁ ⟨⋅⟩ e₂) | Inr ⟨∃ e₁' , ⇰₁ ⟩ = Inr (λ ε → ⟨∃ (e₁' ⟨⋅⟩ e₂) ⦂⦂ ε , Cast/e (App/e₁ ⇰₁) ⟩)
  progress ⟪ e ⦂⦂ ε₁ ⟫ = Inr (λ ε₂ → ⟨∃ e ⦂⦂ ε₂ ⊚ ε₁ , Cast/ε ⟩)
  progress⦂ : ∀ {τ} (e : [] ⊢⦂ τ) → is-val⦂ e ∨ (∃ e' 𝑠𝑡 e ⇰⦂ e')
  progress⦂ (e ⦂⦂ ε) with progress e
  progress⦂ (e ⦂⦂ ε) | Inl val[e] = Inl (Val⦂ val[e])
  progress⦂ (e ⦂⦂ ε) | Inr ⇰₁ = Inr (⇰₁ ε)

----------------
-- Evaluation --
----------------

mutual
  data val : type → Set where
    ⟨𝔹⟩ : 𝔹 → val ⟨𝔹⟩
    ⟨_,_⟩ : ∀ {Γ τ₁ τ₂} → τ₁ ∷ Γ ⊢ τ₂ → env Γ → val (τ₁ ⟨→⟩ τ₂)
  data env : context → Set where
    [] : env []
    _∷_ : ∀ {Γ τ} → val⦂ τ → env Γ → env (τ ∷ Γ)
  data val⦂ : type → Set where
    _⦂⦂_ : ∀ {τ₁ τ₂} → val τ₁ → τ₁ ⋖ τ₂ → val⦂ τ₂

weaken[val][_] : ∀ {τ₁ τ₂} → τ₁ ⋖ τ₂ → val⦂ τ₁ → val⦂ τ₂
weaken[val][ ε₂ ] (v ⦂⦂ ε₁) = v ⦂⦂ ε₂ ⊚ ε₁
  
_[_] : ∀ {Γ τ} → env Γ → τ ⋳ Γ → val⦂ τ
(v ∷ ρ) [ Zero ] = v
(v ∷ ρ) [ Succ x ] = ρ [ x ]

mutual
  data _⊢_⇓_ {Γ} (ρ : env Γ) : ∀ {τ} → Γ ⊢ τ → val⦂ τ → Set where
    ⟨𝔹⟩ : ∀ {b}
      → ρ ⊢ ⟨𝔹⟩ b ⇓ ⟨𝔹⟩ b ⦂⦂ xRx
    ⟨if⟩_⟨then⟩_ : ∀ {τ₁ τ₂} {e₁} {e₂ : Γ ⊢⦂ τ₁} {e₃ : Γ ⊢⦂ τ₂} {v : val⦂ τ₁}
      → ρ ⊢ e₁ ⇓⦂ ⟨𝔹⟩ True ⦂⦂ ⟨𝔹⟩
      → ρ ⊢ e₂ ⇓⦂ v
      → ρ ⊢ ⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃ ⇓ weaken[val][ ⋖⟇/L τ₂ ] v
    ⟨if⟩_⟨else⟩_ : ∀ {τ₁ τ₂} {e₁} {e₂ : Γ ⊢⦂ τ₁} {e₃ : Γ ⊢⦂ τ₂} {v}
      → ρ ⊢ e₁ ⇓⦂ ⟨𝔹⟩ False ⦂⦂ ⟨𝔹⟩
      → ρ ⊢ e₃ ⇓⦂ v
      → ρ ⊢ ⟨if⟩ e₁ ⟨then⟩ e₂ ⟨else⟩ e₃ ⇓ weaken[val][ ⋖⟇/R τ₁ ] v
    Var : ∀ {τ} {x : τ ⋳ Γ}
      → ρ ⊢ Var x ⇓ ρ [ x ]
    ⟨λ⟩ : ∀ {τ₁ τ₂} {e : τ₁ ∷ Γ ⊢ τ₂}
      → ρ ⊢ ⟨λ⟩ e ⇓ ⟨ e , ρ ⟩ ⦂⦂ xRx
    _⟨⋅⟩_ : ∀ {Γ'} {τ₁₁ τ₂₁ τ₁₂ τ₂₂}
        {e₁ : Γ ⊢⦂ τ₁₁ ⟨→⟩ τ₂₁} {e₂ : Γ ⊢⦂ τ₁₁}
        {ρ' : env Γ'} {e' : τ₁₂ ∷ Γ' ⊢ τ₂₂} {ε₁ : τ₁₁ ⋖ τ₁₂} {ε₂ : τ₂₂ ⋖ τ₂₁}
        {v₁ : val⦂ τ₁₁} {v₂ : val⦂ τ₂₂}
      → ρ ⊢ e₁ ⇓⦂ ⟨ e' , ρ' ⟩ ⦂⦂ (ε₁ ⟨→⟩ ε₂)
      → ρ ⊢ e₂ ⇓⦂ v₁
      → weaken[val][ ε₁ ] v₁ ∷ ρ' ⊢ e' ⇓ v₂
      → ρ ⊢ e₁ ⟨⋅⟩ e₂ ⇓ weaken[val][ ε₂ ] v₂
  data _⊢_⇓⦂_ {Γ} (ρ : env Γ) : ∀ {τ} → Γ ⊢⦂ τ → val⦂ τ → Set where
    ⇓⦂⦂ : ∀ {τ₁ τ₂ τ₃} {e : Γ ⊢ τ₂} {ε₂ : τ₂ ⋖ τ₃} {v : val τ₁} {ε₁ : τ₁ ⋖ τ₂}
      → ρ ⊢ e ⇓ v ⦂⦂ ε₁
      → ρ ⊢ e ⦂⦂ ε₂ ⇓⦂ v ⦂⦂ ε₂ ⊚ ε₁
