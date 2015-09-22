module CDGAI.Semantics where

open import Prelude
open import POSet
open import CDGAI.Syntax

⟦_⟧ᵘ : unary → ℤ → ℤ
⟦ [+] ⟧ᵘ = suc⸢ℤ⸣
⟦ [-] ⟧ᵘ = pred⸢ℤ⸣

data _∈⟦_⟧ᵇ[_,_] : ℤ → binary → ℤ → ℤ → Set where
  [+] : ∀ {n₁ n₂} → (n₁ +⸢ℤ⸣ n₂) ∈⟦ [+] ⟧ᵇ[ n₁ , n₂ ]
  [-] : ∀ {n₁ n₂} → (n₁ -⸢ℤ⸣ n₂) ∈⟦ [-] ⟧ᵇ[ n₁ , n₂ ]
  [×] : ∀ {n₁ n₂} → (n₁ *⸢ℤ⸣ n₂) ∈⟦ [×] ⟧ᵇ[ n₁ , n₂ ]
  [/] : ∀ {n₁ n₂} (p : n₂ ≢ Zero) → (n₁ /⸢ℤ⸣ mk-ℤ⁺ n₂ p) ∈⟦ [/] ⟧ᵇ[ n₁ , n₂ ]
  [%] : ∀ {n₁ n₂} (p : n₂ ≢ Zero) → (n₁ %⸢ℤ⸣ mk-ℤ⁺ n₂ p) ∈⟦ [%] ⟧ᵇ[ n₁ , n₂ ]

data env : context → Set where
  [] : env zero
  _∷_ : ∀ {Γ} → ℤ → env Γ → env (Suc Γ)

instance
  env-PreOrder : ∀ {Γ} → PreOrder zeroˡ (env Γ)
  env-PreOrder = ≡-PreOrder

_[_] : ∀ {Γ} → env Γ → var Γ → ℤ
(n ∷ ρ) [ Zero ] = n
(n ∷ ρ) [ Suc x ] = ρ [ x ]

data _⊢_↦_ {Γ} : env Γ → aexp Γ → ℤ → Set where
  Num : ∀ {ρ n} → ρ ⊢ Num n ↦ n
  Var : ∀ {ρ x} → ρ ⊢ Var x ↦ ρ [ x ]
  ⊤ℤ : ∀ {ρ n} → ρ ⊢ ⊤ℤ ↦ n
  Unary : ∀ {ρ o e n} → ρ ⊢ e ↦ n → ρ ⊢ Unary[ o ] e ↦ ⟦ o ⟧ᵘ n
  Binary : ∀ {ρ o e₁ e₂ n₁ n₂ n₃} → ρ ⊢ e₁ ↦ n₁ → ρ ⊢ e₂ ↦ n₂ → n₃ ∈⟦ o ⟧ᵇ[ n₁ , n₂ ] → ρ ⊢ Binary[ o ] e₁ e₂ ↦ n₃

-- Ordered Universe --

⟦_⟧ᵘ⁺ : unary → ⟪ ⇧ ℤ ⇒ ⇧ ℤ ⟫
⟦ o ⟧ᵘ⁺ = witness-x (curry⸢λ↑⸣ id⸢λ↑⸣) $ mk[witness] ⟦ o ⟧ᵘ res-x

⟦_⟧ᵇ⁺ : binary → ⟪ ⇧ ℤ ⇒ ⇧ ℤ ⇒ 𝒫 (⇧ ℤ) ⟫ 
⟦ o ⟧ᵇ⁺ = witness-x (curry⸢λ↑⸣ $ curry⸢λ↑⸣ id⸢ω↑⸣) $ mk[witness] (λ x y z → z ∈⟦ o ⟧ᵇ[ x , y ]) ppr
  where
    abstract
      ppr : proper (_⊴_ ⇉ _⊴_ ⇉ _⊵_ ⇉ [→]) (λ x y z → z ∈⟦ o ⟧ᵇ[ x , y ])
      ppr ↯ ↯ ↯ = id

lookup[_]⁺ : ∀ {Γ} → var Γ → ⟪ ⇧ (env Γ) ⇒ ⇧ ℤ ⟫
lookup[ x ]⁺ = witness-x (curry⸢λ↑⸣ id⸢λ↑⸣) $ mk[witness] (λ ρ → ρ [ x ]) res-x

Faexp[_] : ∀ {Γ} → aexp Γ → ⟪ ⇧ (env Γ) ⇒ 𝒫 (⇧ ℤ) ⟫
Faexp[_] {Γ} e = witness-x (curry⸢λ↑⸣ id⸢ω↑⸣) $ mk[witness] (λ ρ n → ρ ⊢ e ↦ n) ppr
    where
      ppr : proper (_⊴_ ⇉ flip _⊴_ ⇉ [→]) (λ ρ n → ρ ⊢ e ↦ n)
      ppr ↯ ↯ = id

β-Faexp[Num]⸢⊑⸣ : ∀ {Γ} {n : ℤ} {R : ⟪ 𝒫 (⇧ (env Γ)) ⟫} → Faexp[ Num n ] * ⋅ R ⊑ return ⋅ ↑ n
β-Faexp[Num]⸢⊑⸣ {Γ} {n} {R} = ext[𝒫]⸢⊑⸣ H
  where
    H : ∀ {n'} → n' ⋿ Faexp[ Num n ] * ⋅ R → n' ⊑ ↑ n
    H {↑⟨ .n ⟩} (∃𝒫 x ,, x∈R ,, Num) = xRx

β-Faexp[Num]⸢⊒⸣ :
  ∀ {Γ} {n : ℤ} {R : ⟪ 𝒫 (⇧ (env Γ)) ⟫}
  → ∃ ρ 𝑠𝑡 ρ ⋿ R
  → return ⋅ ↑ n ⊑ Faexp[ Num n ] * ⋅ R
β-Faexp[Num]⸢⊒⸣ {Γ} {n} {R} (∃ ρ ,, ρ⋿R) = π₂ return↔⋿ $ ∃𝒫 ρ ,, ρ⋿R ,, Num

β-Faexp[Var] : ∀ {Γ} {x : var Γ} {ρ : ⟪ ⇧ (env Γ) ⟫} → Faexp[ Var x ] ⋅ ρ ≈ return ⋅ (lookup[ x ]⁺ ⋅ ρ)
β-Faexp[Var] {Γ} {x} {↑⟨ ρ ⟩} = ext[𝒫]⸢≈⸣ $ LHS , RHS
  where
    LHS : ∀ {n} → n ⋿ Faexp[ Var x ] ⋅ ↑ ρ → n ⋿ return ⋅ (lookup[ x ]⁺ ⋅ ↑ ρ)
    LHS {↑⟨ .(ρ [ x ]) ⟩} Var = xRx
    RHS : ∀ {n} → n ⋿ return ⋅ (lookup[ x ]⁺ ⋅ ↑ ρ) → n ⋿ Faexp[ Var x ] ⋅ ↑ ρ
    RHS ↑⟨ ↯ ⟩ = Var

β-Faexp[Var]⸢⊙⸣ : ∀ {Γ} {x : var Γ} → Faexp[ Var x ] ≈ pure ⋅ lookup[ x ]⁺
β-Faexp[Var]⸢⊙⸣ = ext[⇒]⸢≈⸣ $ λ {ρ} → β-Faexp[Var] {ρ = ρ}

β-Faexp[⊤ℤ]⸢⊑⸣ : ∀ {Γ} {R : ⟪ 𝒫 (⇧ (env Γ)) ⟫} → Faexp[ ⊤ℤ ] * ⋅ R ⊑ all⁺ (⇧ ℤ)
β-Faexp[⊤ℤ]⸢⊑⸣ {Γ} {R} = ext[𝒫]⸢⊑⸣ $ λ {n} → const $ all-in {x = n}

β-Faexp[Unary] : ∀ {Γ} {o : unary} {e : aexp Γ} {ρ : ⟪ ⇧ (env Γ) ⟫} → Faexp[ Unary[ o ] e ] ⋅ ρ ≈ (pure ⋅ ⟦ o ⟧ᵘ⁺) * ⋅ (Faexp[ e ] ⋅ ρ)
β-Faexp[Unary] {Γ} {o} {e} {ρ} = ext[𝒫]⸢≈⸣ $ LHS , RHS
  where
    LHS : ∀ {n} → n ⋿ Faexp[ Unary[ o ] e ] ⋅ ρ → n ⋿ (pure ⋅ ⟦ o ⟧ᵘ⁺) * ⋅ (Faexp[ e ] ⋅ ρ)
    LHS {↑⟨ .(⟦ o ⟧ᵘ n) ⟩} (Unary {n = n} ρ⊢e↦n) = ∃𝒫 ↑ n ,, ρ⊢e↦n ,, xRx
    RHS : ∀ {n} → n ⋿ (pure ⋅ ⟦ o ⟧ᵘ⁺) * ⋅ (Faexp[ e ] ⋅ ρ) → n ⋿ Faexp[ Unary[ o ] e ] ⋅ ρ
    RHS (∃𝒫 n' ,, ρ⊢e↦n' ,, ↑⟨ ↯ ⟩) = Unary ρ⊢e↦n'

β-Faexp[Unary]⸢⟐⸣ : ∀ {Γ} {o : unary} {e : aexp Γ} → Faexp[ Unary[ o ] e ] ≈ pure ⋅ ⟦ o ⟧ᵘ⁺ ⟐ Faexp[ e ]
β-Faexp[Unary]⸢⟐⸣ = ext[⇒]⸢≈⸣ $ λ {ρ} → β-Faexp[Unary] {ρ = ρ}

β-Faexp[Binary]⸢*⸣⸢⋿⸣ :
  ∀ {Γ} {o : binary} {e₁ e₂ : aexp Γ} {R : ⟪ 𝒫 (⇧ (env Γ)) ⟫} {n : ⟪ ⇧ ℤ ⟫}
  → n ⋿ Faexp[ Binary[ o ] e₁ e₂ ] * ⋅ R → n ⋿ (uncurry⁺ ⋅ ⟦ o ⟧ᵇ⁺) * ⋅ (γ⸢IA⸣ ⋅ (Faexp[ e₁ ] * ⋅ R ,⁺ Faexp[ e₂ ] * ⋅ R))
β-Faexp[Binary]⸢*⸣⸢⋿⸣ {n = n} (∃𝒫 ρ ,, ρ∈R ,, Binary {n₁ = n₁} {n₂} {.(↓ n)} ρ⊢e₁↦n₁ ρ⊢e↦n₂ n₃∈⟦o⟧ᵇ[n₁,n₂]) =
  ∃𝒫 ↑⟨ ↑ n₁ , ↑ n₂ ⟩ ,, (∃𝒫 ρ ,, ρ∈R ,, ρ⊢e₁↦n₁) ,  (∃𝒫 ρ ,, ρ∈R ,, ρ⊢e↦n₂) ,, n₃∈⟦o⟧ᵇ[n₁,n₂]

β-Faexp[Binary]⸢*⸣⸢⊑⸣ :
  ∀ {Γ} {o : binary} {e₁ e₂ : aexp Γ} {R : ⟪ 𝒫 (⇧ (env Γ)) ⟫}
  → Faexp[ Binary[ o ] e₁ e₂ ] * ⋅ R ⊑ (uncurry⁺ ⋅ ⟦ o ⟧ᵇ⁺) * ⋅ (γ⸢IA⸣ ⋅ (Faexp[ e₁ ] * ⋅ R ,⁺ Faexp[ e₂ ] * ⋅ R))
β-Faexp[Binary]⸢*⸣⸢⊑⸣ = ext[𝒫]⸢⊑⸣ $ λ {n} → β-Faexp[Binary]⸢*⸣⸢⋿⸣ {n = n}

-- THM : ∀ {Γ} {e : aexp Γ} → Faexp[ e ] * ⋅ (γ ⋅ ρ) ⊑ γ * ⋅ Faexp[ e ] ρ

-- β-Faexp[Binary] :
--   ∀ {Γ} {o : binary} {e₁ e₂ : aexp Γ} {ρ : ⟪ ⇧ (env Γ) ⟫}
--   → Faexp[ Binary[ o ] e₁ e₂ ] ⋅ ρ ≈ (↑uncurry ⋅ ↑⟦ o ⟧ᵇ) * ⋅ (γ[IA] ⋅ (Faexp[ e₁ ] ⋅ ρ ⟨,⟩ Faexp[ e₂ ] ⋅ ρ))
-- β-Faexp[Binary] {Γ} {o} {e₁} {e₂} {ρ} = ext[ω]⸢≈⸣ $ LHS , RHS
--   where
--     LHS : ∀ {n} → n ⋿ Faexp[ Binary[ o ] e₁ e₂ ] ⋅ ρ → n ⋿ (↑uncurry ⋅ ↑⟦ o ⟧ᵇ) * ⋅ (γ[IA] ⋅ (Faexp[ e₁ ] ⋅ ρ ⟨,⟩ Faexp[ e₂ ] ⋅ ρ))
--     LHS {↑⟨ .n₃ ⟩} (Binary {n₁ = n₁} {n₂} {n₃} ρ⊢e₁↦n₁ ρ⊢e₁↦n₂ n∈⟦o⟧[n₁,n₂]) = ∃𝒫 ↑ n₁ ⟨,⟩ ↑ n₂ ,, ρ⊢e₁↦n₁ , ρ⊢e₁↦n₂ ,, n∈⟦o⟧[n₁,n₂]
--     RHS : ∀ {n} → n ⋿ (↑uncurry ⋅ ↑⟦ o ⟧ᵇ) * ⋅ (γ[IA] ⋅ (Faexp[ e₁ ] ⋅ ρ ⟨,⟩ Faexp[ e₂ ] ⋅ ρ)) → n ⋿ Faexp[ Binary[ o ] e₁ e₂ ] ⋅ ρ
--     RHS (∃𝒫 ↑⟨ n₁ , n₂ ⟩ ,, ρ⊢e₁↦n₁ , ρ⊢e₂↦n₂ ,, n∈⟦o⟧[n₁,n₂]) = Binary ρ⊢e₁↦n₁ ρ⊢e₂↦n₂ n∈⟦o⟧[n₁,n₂]
-- 
-- β-Faexp[Binary]⸢⊙⸣ : ∀ {Γ} {o : binary} {e₁ e₂ : aexp Γ} → Faexp[ Binary[ o ] e₁ e₂ ] ≈ ↑uncurry ⋅ ↑⟦ o ⟧ᵇ ⟐ (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ]) ⊙ ↑split)
-- β-Faexp[Binary]⸢⊙⸣ = ext[λ]⸢≈⸣ $ λ {ρ} → β-Faexp[Binary] {ρ = ρ}

-- β-Faexp[Binary]⸢*⸣⸢⊑⸣ :
--   ∀ {Γ} {o : binary} {e₁ e₂ : aexp Γ}
--   → Faexp[ Binary[ o ] e₁ e₂ ] * ⊑ (↑uncurry ⋅ ↑⟦ o ⟧ᵇ) * ⊙ (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] * ⟨,⟩ Faexp[ e₂ ] * ) ⊙ ↑split)
-- β-Faexp[Binary]⸢*⸣⸢⊑⸣ {o = o} {e₁} {e₂} = [⊑-proof-mode]
--   do [⊑][[ Faexp[ Binary[ o ] e₁ e₂ ] * ]]
--   ⊑‣ [⊑-focus-in [*] ] [⊑-≈] (↑uncurry ⋅ ↑⟦ o ⟧ᵇ ⟐ (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ]) ⊙ ↑split)) ⟅ β-Faexp[Binary]⸢⊙⸣  ⟆
--   ⊑‣ [⊑][[ (↑uncurry ⋅ ↑⟦ o ⟧ᵇ ⟐ (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ]) ⊙ ↑split)) * ]]
--   ⊑‣ [⊑-≈] (↑uncurry ⋅ ↑⟦ o ⟧ᵇ) * ⊙ (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ]) ⊙ ↑split) * ⟅ associative[⟐]⸢⊙⸣ ⟆
--   ⊑‣ [⊑-focus-right [⊙] 𝑜𝑓 (↑uncurry ⋅ ↑⟦ o ⟧ᵇ) * ] begin
--        do [⊑][[ (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ]) ⊙ ↑split) * ]]
--        ⊑‣ [⊑-focus-in [*] ] [⊑-≈] (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ])) ⊙ ↑split ⟅ ◇ associative[⊙] ⟆
--        ⊑‣ [⊑][[ ((γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ])) ⊙ ↑split) * ]]
--        ⊑‣ [⊑-≈] (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ])) * ⊙ (pure ⋅ ↑split) * ⟅ ◇ right-unit[*]⸢X⸣⸢⊙⸣ ⟆
--        ⊑‣ [⊑-focus-right [⊙] 𝑜𝑓 (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ])) * ] [⊑] γ[IA] ⊙ ↑split ⟅ {!!} ⟆
--        ⊑‣ [⊑][[  (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ])) * ⊙ (γ[IA] ⊙ ↑split) ]]
--        ⊑‣ [⊑-≈]  ((γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ])) * ⊙ γ[IA]) ⊙ ↑split ⟅ ◇ associative[⊙] ⟆
--        ⊑‣ [⊑-focus-left [⊙] 𝑜𝑓 ↑split ] begin
--             do [⊑][[ (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ])) * ⊙ γ[IA] ]]
--             ⊑‣ {!!}
--             ⊑‣ [⊑][[ γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] * ⟨,⟩ Faexp[ e₂ ] *) ]]
--             end
--        ⊑‣ [⊑][[ (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] * ⟨,⟩ Faexp[ e₂ ] * )) ⊙ ↑split ]]
--        ⊑‣ [⊑-≈] γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] * ⟨,⟩ Faexp[ e₂ ] * ) ⊙ ↑split ⟅ associative[⊙] ⟆
--        end
--   ⊑‣ [⊑][[ (↑uncurry ⋅ ↑⟦ o ⟧ᵇ) * ⊙ (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] * ⟨,⟩ Faexp[ e₂ ] * ) ⊙ ↑split) ]]
--   ⬜
-- 
--   (γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ])) *                    : 𝒫 (A × A) → 𝒫 (A × A)
-- ⊑ γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] * ⟨,⟩ Faexp[ e₂ ] *) ⊙ pure ⋅ η[IA]     : 
-- 
-- γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] ⟨,⟩ Faexp[ e₂ ])                        : (A × A) → 𝒫 (A × A)
-- γ[IA] ⊙ ↑apply⸢×⸣ ⋅ (Faexp[ e₁ ] * ⟨,⟩ Faexp[ e₂ ] *) ⊙ pure ⋅ η[IA]     :  (A × A) → 𝒫 (A × A)
-- 
-- apply (F[ e₁ ] , F[ e₂ ]) : (A × A) → (𝒫 A × 𝒫 A)
-- apply (F[ e, ] * , F[ e₂ ] *) ⊙ η[IA] : (A × A) → (𝒫 A × 𝒫 A)
-- 
-- (pure ⋅ split) * : 𝒫 A → 𝒫 (A × A)
-- γ[IA] ⊙ split : 𝒫 A → 𝒫 (A × A)

