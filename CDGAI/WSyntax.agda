module CDGAI.WSyntax where

open import Prelude
open import Poset
open import CDGAI.ASyntax
open import CDGAI.ASemantics
open import CDGAI.BSyntax
open import CDGAI.BSemantics

-- Programs (wexp*) and statements (wexp)

mutual
  data wexp (Γ : context) : Set where
    Skip : wexp Γ
    Assign : var Γ → aexp Γ → wexp Γ
    If : bexp Γ → sexp Γ → sexp Γ → wexp Γ
    While : bexp Γ → sexp Γ → wexp Γ

  data sexp (Γ : context) : Set where
    [] : sexp Γ
    _∷_ : wexp Γ → sexp Γ → sexp Γ

_⧺ˢ_ : ∀ {Γ} → sexp Γ → sexp Γ → sexp Γ
[] ⧺ˢ s = s
(w ∷ s₁) ⧺ˢ s₂ = w ∷ (s₁ ⧺ˢ s₂)

program : context → Set
program Γ = sexp Γ

data wconfig (Γ : context) : Set where
  ⟨_,_⟩ : wexp Γ → env Γ → wconfig Γ

data sconfig (Γ : context) : Set where
  ⟨_,_⟩ : sexp Γ → env Γ → sconfig Γ

instance
  PreOrder[wexp] : ∀ {Γ} → Precision 0ᴸ (wexp Γ)
  PreOrder[wexp] = mk[Precision] _≡_
  PreOrder[sexp] : ∀ {Γ} → Precision 0ᴸ (sexp Γ)
  PreOrder[sexp] = mk[Precision] _≡_
  PreOrder[sconfig] : ∀ {Γ} → Precision 0ᴸ (sconfig Γ)
  PreOrder[sconfig] = mk[Precision] _≡_

module _ {Γ} where
  []ˢ♮ : ⟪ ⇧ (sexp Γ) ⟫
  []ˢ♮ = ♮⟨ [] ⟩
  
  [⧺ˢ] : ⟪ ⇧ (sexp Γ) ↗ ⇧ (sexp Γ) ↗ ⇧ (sexp Γ) ⟫
  [⧺ˢ] = witness (curry⸢λ♭⸣ $ curry⸢λ♭⸣ id⸢λ♭⸣) $ mk[witness] _⧺ˢ_ ppr
    where
      ppr : proper (_≡_ ⇉ _≡_ ⇉ _≡_) _⧺ˢ_
      ppr ↯ ↯ = ↯
  
  _⧺ˢ♮_ : ⟪ ⇧ (sexp Γ) ⟫ → ⟪ ⇧ (sexp Γ) ⟫ → ⟪ ⇧ (sexp Γ) ⟫
  s₁ ⧺ˢ♮ s₂ = [⧺ˢ] ⋅ s₁ ⋅ s₂

  appendingˢ♮ : ⟪ ⇧ (sexp Γ) ↗ ⇧ (sexp Γ) ↗ ⇧ (sexp Γ) ⟫
  appendingˢ♮ = witness (curry⸢λ⸣ $ curry⸢λ⸣ id⸢λ⸣) $ mk[witness] (λ y x → x ⧺ˢ♮ y) (λ ⊑₁ ⊑₂ → res[fx][↗]⸢⊑⸣ (res[x][↗]⸢⊑⸣ {f = [⧺ˢ]} ⊑₂) ⊑₁)

-- Programs and statements annotated with a unique number

mutual
  data wexpᴬ (n : ℕ) (Γ : context) : Set where
    _ː_ : fin n → wexp-recᴬ n Γ → wexpᴬ n Γ

  data wexp-recᴬ (n : ℕ) (Γ : context) : Set where
    Skip : wexp-recᴬ n Γ
    Assign : var Γ → aexp Γ → wexp-recᴬ n Γ
    If : bexp Γ → wexpᴬ* n Γ → wexpᴬ* n Γ → wexp-recᴬ n Γ
    While : bexp Γ → wexpᴬ* n Γ → wexp-recᴬ n Γ

  wexpᴬ* : ℕ → context → Set
  wexpᴬ* n Γ = list (wexpᴬ n Γ)

wmap : ℕ → context → Set
wmap n Γ = 𝕍 n (wexpᴬ n Γ)

-- Stamping programs into annotated programs

-- mutual
--   stamp-recʷ :
--     ∀ {Γ}                                        -- FYI: to help your intuition, (I) means "input" and (O) means "output"
--     → wexp Γ                                     -- (I) the expression to stamp
--     → ∀ (i : ℕ)                                  -- (I) the given stamp (for this expression)
--     → ∃ i' ⦂ ℕ                                   -- (O) the returned stamp (for the caller's next expressions)
--     𝑠𝑡 i ≤ i'                                    -- (O) a proof that the returned stamp is larger than the given one
--     ∧ (∀ (n : ℕ)                                 -- (I) a strict upper bound on the total number of stamps
--        → i' ≤ n                                  -- (I) a proof that the strict uppber bound is larger than the returned stamp
--        → wexpᴬ n Γ                               -- (O) an expression with stamp `i`, proven to be less than `n`
--        ∧ ( (𝕍 i (wexpᴬ n Γ) → 𝕍 n (wexpᴬ n Γ))
--          → (𝕍 i' (wexpᴬ n Γ) → 𝕍 n (wexpᴬ n Γ)))) -- (O) a list-builder (called a diff list by some, often attributed to Hughes)
--   stamp-recʷ {Γ} Skip i =
--      ⟨∃ Succ i
--      , ⟨ weaken[≤]ⁿ xRx
--        , (λ n m≤n →
--           let wᴬ = ⟨ mk[fin/<] i {!!} {- m≤n -} , Skip ⟩
--           in ⟨ wᴬ , (λ i↦wexp → {!!}) ⟩) -- i↦wexp ∘ _∷_ wᴬ)
--        ⟩
--      ⟩
--   stamp-recʷ {Γ} (Assign x ae) i =
--     ⟨∃ Succ i
--     , ⟨ weaken[≤]ⁿ xRx
--       , (λ n m≤n →
--           let wᴬ = ⟨ mk[fin/<] i {!!} {- m≤n -} , Assign x ae ⟩
--           in ⟨ wᴬ , (λ i↦wexp → {!!}) ⟩) -- i↦wexp ∘ _∷_ wᴬ)
--       ⟩
--     ⟩
--   stamp-recʷ {Γ} (If be ws₁ ws₂) i₀ with stamp-recˢ ws₁ i₀
--   … | ⟨∃ i₁ , ⟨ i₀≤i₁ , k₁ ⟩ ⟩ with stamp-recˢ ws₂ i₁
--   … | ⟨∃ i₂ , ⟨ i₁≤i₂ , k₂ ⟩ ⟩ =
--      ⟨∃ Succ i₂
--      , ⟨ weaken[≤]ⁿ xRx ⊚ i₁≤i₂ ⊚ i₀≤i₁
--        , (λ n suc[i₂]≤n →
--           let i₂≤n = suc[i₂]≤n ⊚ weaken[≤]ⁿ xRx
--               ⟨ wsᴬ₁ , i₁↦wexp ⟩ = k₁ n (i₂≤n ⊚ i₁≤i₂)
--               ⟨ wsᴬ₂ , i₂↦wexp ⟩ = k₂ n i₂≤n
--               wᴬ = ⟨ mk[fin/<] i₂ {!!} {- suc[i₂]≤n -} , If be wsᴬ₁ wsᴬ₂ ⟩
--           in ⟨ wᴬ , {!!} ⟩)
--        ⟩
--      ⟩ -- i₁↦wexp ∘ i₂↦wexp ∘ (λ x → x ∘ _∷_ wᴬ)) -- wᴬ ∷ i₂↦wexp)
--   stamp-recʷ {Γ} (While be ws) i₀ with stamp-recˢ ws i₀
--   … | ⟨∃ i₁ , ⟨ i₀≤i₁ , k ⟩ ⟩ =
--      ⟨∃ Succ i₁
--      , ⟨ weaken[≤]ⁿ xRx ⊚ i₀≤i₁
--        , (λ n suc[i₁]≤n →
--          let ⟨ wsᴬ , i₁↦wexp ⟩ = k n {!!} {- (weaken[≤]ⁿ suc[i₁]≤n) -}
--              wᴬ = ⟨ mk[fin/<] i₁ {!!} {- suc[i₁]≤n -} , While be wsᴬ ⟩
--          in ⟨ wᴬ , {!!} ⟩) -- i₁↦wexp ∘ (λ x → x ∘ _∷_ wᴬ))
--        ⟩
--      ⟩
--   stamp-recˢ :
--     ∀ {Γ}
--     → wexp* Γ → ∀ (i : ℕ) →                    -- (I)
--     ∃ i' ⦂ ℕ 𝑠𝑡 i ≤ i'                         -- (O)
--     ∧ (∀ (n : ℕ) → i' ≤ n                      -- (I)
--     → wexp*ᴬ n Γ                               -- (O)
--     ∧ ( (𝕍 i (wexpᴬ n Γ) → 𝕍 n (wexpᴬ n Γ))
--       → (𝕍 i' (wexpᴬ n Γ) → 𝕍 n (wexpᴬ n Γ))))  -- (O)
--   stamp-recˢ [] i = ⟨∃ i , ⟨ xRx , (λ n i≤n → ⟨ [] , id ⟩) ⟩ ⟩
--   stamp-recˢ (w ∷ ws) i₀ with stamp-recʷ w i₀
--   … | ⟨∃ i₁ , ⟨ i₀≤i₁ , k₁ ⟩ ⟩ with stamp-recˢ ws i₁
--   … | ⟨∃ i₂ , ⟨ i₁≤i₂ , k₂ ⟩ ⟩ =
--      ⟨∃ i₂
--      , ⟨ i₁≤i₂ ⊚ i₀≤i₁
--        , (λ n i₂≤n →
--            let ⟨ wᴬ , i₁↦wexp ⟩ = k₁ n (i₂≤n ⊚ i₁≤i₂)
--                ⟨ wsᴬ , i₂↦wexp ⟩ = k₂ n i₂≤n
--            in ⟨ wᴬ ∷ wsᴬ , {!!} ⟩) -- i₁↦wexp ∘ i₂↦wexp)
--        ⟩
--      ⟩
-- 
-- stamp : ∀ {Γ} → wexp* Γ → ∃ n ⦂ ℕ 𝑠𝑡 wexp*ᴬ n Γ ∧ 𝕍 n (wexpᴬ n Γ)
-- stamp ws with stamp-recˢ ws 0
-- … | ⟨∃ i' , ⟨ 0≤i' , k ⟩ ⟩ with k i' xRx
-- … | ⟨ wsᴬ , bldr ⟩ = ⟨∃ i' , ⟨ wsᴬ , {!!} ⟩ ⟩ -- bldr id []
-- 
-- %e₁ : wexp 1
-- %e₁ = Assign Zero (Num (𝕫ⁿ 1))
-- 
-- test-stamp-%e₁ : stamp (%e₁ ∷ (Skip ∷ [])) ≡
--   let %e₁ᴬ = ⟨ Zero     , Assign Zero (Num (𝕫ⁿ 1)) ⟩
--       %e₂ᴬ = ⟨ Succ Zero , Skip ⟩
--   in ⟨∃ 2 , ⟨ %e₁ᴬ ∷ (%e₂ᴬ ∷ []) , %e₁ᴬ ∷ (%e₂ᴬ ∷ []) ⟩ ⟩
-- test-stamp-%e₁ = {!↯!}
