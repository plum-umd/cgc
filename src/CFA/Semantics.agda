module CFA.Semantics where

open import Prelude
open import POSet

open import CFA.Syntax

mutual
  data value Γ : Set where
    FClo : var Γ → var Γ → call Γ → env Γ → value Γ
    KClo : var Γ → call Γ → env Γ → value Γ
    Stop : value Γ
    Undefined : value Γ

  data env[_] Γ : ℕ → Set where
    []  : env[ Γ ] 0
    _∷_ : ∀ {n} → value Γ → env[ Γ ] n → env[ Γ ] (Suc n)

  env : context → Set
  env Γ = env[ Γ ] Γ

instance
  PreOrder[value] : ∀ {Γ} → PreOrder zeroˡ (value Γ)
  PreOrder[value] = ≡-PreOrder

  PreOrder[env] : ∀ {Γ} → PreOrder zeroˡ (env Γ)
  PreOrder[env] = ≡-PreOrder

data is[FClo] {Γ} : value Γ → Set where
  Is : ∀ {x k c ρ} → is[FClo] (FClo x k c ρ)

data is[KClo] {Γ} : value Γ → Set where
  Is : ∀ {x c ρ} → is[KClo] (KClo x c ρ)

lookup⸢env⸣ : ∀ {Γ n} → var n → env[ Γ ] n → value Γ
lookup⸢env⸣ Zero (v ∷ ρ) = v
lookup⸢env⸣ (Suc x) (v ∷ ρ) = lookup⸢env⸣ x ρ

_[_↦_]⸢env⸣ : ∀ {Γ n} → env[ Γ ] n → var n → value Γ → env[ Γ ] n
(v₁ ∷ ρ) [ Zero  ↦ v₂ ]⸢env⸣ = v₂ ∷ ρ
(v₁ ∷ ρ) [ Suc x ↦ v₂ ]⸢env⸣ = v₁ ∷ ρ [ x ↦ v₂ ]⸢env⸣

data _∈⸢env⸣_ {Γ} : ∀ {n} → value Γ → env[ Γ ] n → Set where
  Zero : ∀ {n} {ρ : env[ Γ ] n} {v} → v ∈⸢env⸣ (v ∷ ρ)
  Suc : ∀ {n} {ρ : env[ Γ ] n} {v₁ v₂} → v₂ ∈⸢env⸣ ρ → v₂ ∈⸢env⸣ (v₁ ∷ ρ)

data [_,_]∈⸢env⸣ {Γ} : ∀ {n} → var n → value Γ → env[ Γ ] n → Set where
  Zero : ∀ {n} {ρ : env[ Γ ] n} {v} → [ Zero , v ]∈⸢env⸣ (v ∷ ρ)
  Suc : ∀ {n} {ρ : env[ Γ ] n} {x v₁ v₂} → [ x , v₂ ]∈⸢env⸣ ρ → [ Suc x , v₂ ]∈⸢env⸣ (v₁ ∷ ρ)

∈-lookup⸢env⸣ : ∀ {Γ n} (x : var n) (ρ : env[ Γ ] n) → [ x , lookup⸢env⸣ x ρ ]∈⸢env⸣ ρ
∈-lookup⸢env⸣ Zero    (v ∷ ρ) = Zero
∈-lookup⸢env⸣ (Suc x) (v ∷ ρ) = Suc (∈-lookup⸢env⸣ x ρ)

∈-lookup⸢env⸣-≡ : ∀ {Γ n} {x : var n} {v : value Γ} {ρ : env[ Γ ] n} → [ x , v ]∈⸢env⸣ ρ → lookup⸢env⸣ x ρ ≡ v
∈-lookup⸢env⸣-≡ {x = Zero}  {v}  {.v ∷ ρ} Zero    = ↯
∈-lookup⸢env⸣-≡ {x = Suc x} {v₂} {v₁ ∷ ρ} (Suc P) = ∈-lookup⸢env⸣-≡ P

empty⸢env⸣ : ∀ {Γ n} → env[ Γ ] n
empty⸢env⸣ {n = Zero} = []
empty⸢env⸣ {n = Suc n} = Undefined ∷ empty⸢env⸣

⟦_⟧ : ∀ {Γ} → atom Γ → env Γ → value Γ
⟦ Var x ⟧  ρ = lookup⸢env⸣ x ρ
⟦ FLam x k c ⟧ ρ = FClo x k c ρ
⟦ KLam x c ⟧ ρ = KClo x c ρ

data config Γ : Set where
  ⟨_,_⟩ : call Γ → env Γ → config Γ

instance
  PreOrder[config] : ∀ {Γ} → PreOrder zeroˡ (config Γ)
  PreOrder[config] = ≡-PreOrder

data _~~>_ {Γ} : config Γ → config Γ → Set where
  Apply :
    ∀ {x k c ρ' ρ fa₁ fa₂ ka}
    → ⟦ fa₁ ⟧ ρ ≡ FClo x k c ρ'
    → ⟨ Apply fa₁ fa₂ ka , ρ ⟩ ~~> ⟨ c , ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣ [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣ ⟩
  Call :
    ∀ {x c ρ' ρ ka fa}
    → ⟦ ka ⟧ ρ ≡ KClo x c ρ'
    → ⟨ Call ka fa , ρ ⟩ ~~> ⟨ c , ρ' [ x ↦ ⟦ fa ⟧ ρ ]⸢env⸣ ⟩

monotonic[~~>] : ∀ {Γ} {ς₁ ς₂ : config Γ} → ς₁ ≡ ς₂ → ∀ {ς₁' ς₂'} → ς₂' ≡ ς₁' → ς₁ ~~> ς₁' → ς₂ ~~> ς₂'
monotonic[~~>] ↯ ↯ = id

initial : ∀ {Γ} → program Γ → config (Suc Γ)
initial c = ⟨ suc⸢call⸣ c , empty⸢env⸣ [ Zero ↦ Stop ]⸢env⸣ ⟩

data [_]_##>_ {Γ} (p : program Γ) (ς : config (Suc Γ)) : config (Suc Γ) → Set where
  Initial : [ p ] ς ##> initial p
  Step    : ∀ {ς'} → ς ~~> ς' → [ p ] ς ##> ς'

↑steps⸢𝒫⸣ : ∀ {Γ} → ⟪ ⇧ (config Γ) ⇒ 𝒫 (⇧ (config Γ)) ⟫
↑steps⸢𝒫⸣ {Γ} = witness-x (curry⸢λ↑⸣ id⸢ω↑⸣) $ mk[witness] fun ppr
  where
    fun : config Γ → config Γ → Set zeroˡ
    fun ς ς' = ς ~~> ς'
    abstract
      ppr : proper (_⊴_ ⇉ _⊵_ ⇉ [→]) fun
      ppr ↯ ↯ = id

postulate
  config→× : ∀ {Γ} → ⟪ ⇧ (config Γ) ⇒ ⇧ (call Γ) ×⁺ ⇧ (env Γ) ⟫
  -- config→× = {!!}
  
  ×→config : ∀ {Γ} → ⟪ ⇧ (call Γ) ×⁺ ⇧ (env Γ) ⇒ ⇧ (config Γ) ⟫
  -- ×→config = {!!}
  
  ↑steps⸢×𝒫⸣ : ∀ {Γ} → ⟪ 𝒫 (⇧ (call Γ)) ×⁺ 𝒫 (⇧ (env Γ)) ⇒ 𝒫 (⇧ (call Γ)) ×⁺ 𝒫 (⇧ (env Γ)) ⟫
  -- ↑steps⸢×𝒫⸣ = {!!} ⊙ (pure ⋅ config→×) * ⊙ ↑steps⸢𝒫⸣ * ⊙ (pure ⋅ ×→config) * ⊙ γ⸢IA⸣


-- -- Decision procedure for ~~> --
-- 
-- decideFClo : ∀ {Γ} (v : value Γ) → pred-decision is[FClo] v
-- decideFClo (FClo x k c ρ) = Yes Is
-- decideFClo (KClo x c ρ) = No $ λ ()
-- decideFClo Stop = No (λ ())
-- decideFClo Undefined = No $ λ ()
-- 
-- decideKClo : ∀ {Γ} (v : value Γ) → pred-decision is[KClo] v
-- decideKClo (FClo x k c ρ) = No $ λ ()
-- decideKClo (KClo x c ρ) = Yes Is
-- decideKClo Stop = No (λ ())
-- decideKClo Undefined = No (λ ())
-- 
-- decideLookup : ∀ {𝓁'} {Γ n} {P : predicate 𝓁' (value Γ)} (f : ∀ (v : value Γ) → pred-decision P v) (ρ : env[ Γ ] n) (x : var n) → pred-decision P (lookup⸢env⸣ x ρ)
-- decideLookup f (v ∷ ρ) Zero = f v
-- decideLookup f (v ∷ ρ) (Suc x) = decideLookup f ρ x
-- 
-- decideDenote : ∀ {𝓁'} {Γ} {P : predicate 𝓁' (value Γ)} (f : ∀ (v : value Γ) → pred-decision P v) (ρ : env Γ) (fa : atom Γ) → pred-decision P (⟦ fa ⟧ ρ)
-- decideDenote f ρ (Var x) = decideLookup f ρ x
-- decideDenote f ρ (FLam x k c) = f (FClo x k c ρ)
-- decideDenote f ρ (KLam x c) = f (KClo x c ρ)
-- 
-- steps⸢↯-F-Yes-LHS⸣ :
--   ∀ {Γ} {ρ : env Γ} {fa₁ fa₂ ka x k c ρ'} → ⟦ fa₁ ⟧ ρ ≡ FClo x k c ρ' → ∀ {ς'}
--   → ς' ∈⸢list-set⸣ single⸢list-set⸣ ⟨ c , ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣ [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣ ⟩ → ⟨ Apply fa₁ fa₂ ka , ρ ⟩ ~~> ς'
-- steps⸢↯-F-Yes-LHS⸣ ⟦fa₁⟧≡clo Zero = Apply ⟦fa₁⟧≡clo
-- steps⸢↯-F-Yes-LHS⸣ ⟦fa₁⟧≡clo (Suc ())
-- steps⸢↯-F-Yes-RHS⸣ :
--   ∀ {Γ} {ρ : env Γ} {fa₁ fa₂ ka x k c ρ'} → ⟦ fa₁ ⟧ ρ ≡ FClo x k c ρ' → ∀ {ς'}
--   → ⟨ Apply fa₁ fa₂ ka , ρ ⟩ ~~> ς' → ς' ∈⸢list-set⸣ single⸢list-set⸣ ⟨ c , ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣ [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣ ⟩
-- steps⸢↯-F-Yes-RHS⸣ ⟦fa₁⟧≡clo (Apply ⟦fa₁⟧≡clo') with ⟦fa₁⟧≡clo ⌾ ◇ ⟦fa₁⟧≡clo'
-- ... | ↯ = Zero
-- 
-- steps⸢↯-F-No-RHS⸣ : ∀ {Γ} {ρ : env Γ} {fa₁ fa₂ ka} → not (is[FClo] $ ⟦ fa₁ ⟧ ρ) → ∀ {ς'} → ⟨ Apply fa₁ fa₂ ka , ρ ⟩ ~~> ς' → ς' ∈⸢list-set⸣ []
-- steps⸢↯-F-No-RHS⸣ not[clo] (Apply ⟦fa₁⟧ρ≡clo) rewrite ⟦fa₁⟧ρ≡clo = exfalso $ not[clo] Is
-- 
-- -- step⸢↯-K-Yes-LHS⸣
-- 
-- steps⸢↯⸣-w/spec : ∀ {Γ} (ς : config Γ) → ∃ ςs 𝑠𝑡 (∀ {ς'} → ς' ∈⸢list-set⸣ ςs ↔ ς ~~> ς')
-- steps⸢↯⸣-w/spec {Γ} ⟨ Apply fa₁ fa₂ ka , ρ ⟩ with ⟦ fa₁ ⟧ ρ | remember ⟦ fa₁ ⟧ ρ | decideDenote decideFClo ρ fa₁
-- ... | .(FClo x k c ρ') | Was ≡⟦fa₁⟧ρ | Yes (Is {x} {k} {c} {ρ'}) = ∃ single⸢list-set⸣ ⟨ c , (ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣) [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣ ⟩ ,, LHS , RHS
--   where
--     LHS : ∀ {ς'} → ς' ∈⸢list-set⸣ single⸢list-set⸣ ⟨ c , ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣ [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣ ⟩ → ⟨ Apply fa₁ fa₂ ka , ρ ⟩ ~~> ς'
--     LHS Zero = Apply $ ◇ ≡⟦fa₁⟧ρ
--     LHS (Suc ())
--     RHS : ∀ {ς'}  → ⟨ Apply fa₁ fa₂ ka , ρ ⟩ ~~> ς' → ς' ∈⸢list-set⸣ single⸢list-set⸣ ⟨ c , ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣ [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣ ⟩
--     RHS (Apply ⟦fa₁⟧ρ≡clo) with ⟦fa₁⟧ρ≡clo ⌾ ≡⟦fa₁⟧ρ
--     ... | ↯ = Zero
-- ... | v | Was ≡⟦fa₁⟧ρ | No not[clo] = ∃ [] ,, (λ ()) , RHS
--   where
--     RHS : ∀ {ς'} → ⟨ Apply fa₁ fa₂ ka , ρ ⟩ ~~> ς' → ς' ∈⸢list-set⸣ []
--     RHS (Apply ⟦fa₁⟧ρ≡clo) = exfalso $ not[clo] $ change-goal (res-x {f = is[FClo]} $ ⟦fa₁⟧ρ≡clo ⌾ ≡⟦fa₁⟧ρ) Is
-- steps⸢↯⸣-w/spec ⟨ Call ka fa , ρ ⟩ with ⟦ ka ⟧ ρ | remember ⟦ ka ⟧ ρ | decideDenote decideKClo ρ ka
-- ... | .(KClo x c ρ') | Was ≡⟦ka⟧ρ | Yes (Is {x} {c} {ρ'}) = ∃ single⸢list-set⸣ ⟨ c , ρ' [ x ↦ ⟦ fa ⟧ ρ ]⸢env⸣ ⟩ ,, LHS , RHS
--   where
--     LHS : ∀ {ς'} → ς' ∈⸢list-set⸣ single⸢list-set⸣ ⟨ c , ρ' [ x ↦ ⟦ fa ⟧ ρ ]⸢env⸣ ⟩ → ⟨ Call ka fa , ρ ⟩ ~~> ς'
--     LHS Zero = Call $ ◇ ≡⟦ka⟧ρ
--     LHS (Suc ())
--     RHS : ∀ {ς'} → ⟨ Call ka fa , ρ ⟩ ~~> ς' → ς' ∈⸢list-set⸣ single⸢list-set⸣ ⟨ c , ρ' [ x ↦ ⟦ fa ⟧ ρ ]⸢env⸣ ⟩
--     RHS (Call ⟦ka⟧ρ≡clo) with ⟦ka⟧ρ≡clo ⌾ ≡⟦ka⟧ρ
--     ... | ↯ = Zero
-- ... | v | Was ≡⟦ka⟧ρ | No not[clo] = ∃ [] ,, (λ ()) , RHS
--   where
--     RHS : ∀ {ς'} → ⟨ Call ka fa , ρ ⟩ ~~> ς' → ς' ∈⸢list-set⸣ []
--     RHS (Call ⟦ka⟧ρ≡clo) = exfalso $ not[clo] $ change-goal (res-x {f = is[KClo]} $ ⟦ka⟧ρ≡clo ⌾ ≡⟦ka⟧ρ) Is
-- 
-- steps⸢↯⸣ : ∀ {Γ} → config Γ → list-set (config Γ)
-- steps⸢↯⸣ ς = dπ₁ $ steps⸢↯⸣-w/spec ς
-- 
-- -- Ordered Universe --
-- 
-- [,,] : ∀ {Γ} → ⟪ ⇧ (call Γ) ⇒ ⇧ (env Γ) ⇒ ⇧ (config Γ) ⟫
-- [,,] {Γ} = witness-x (curry⸢λ↑⸣ $ curry⸢λ↑⸣ id⸢λ↑⸣) $ mk[witness] fun ppr
--   where
--     fun : call Γ → env Γ → config Γ
--     fun = ⟨_,_⟩
--     abstract
--       ppr : proper (_⊴_ ⇉ _⊴_ ⇉ _⊴_) fun
--       ppr ↯ ↯ = ↯
-- 
-- _⟨,,⟩_ : ∀ {Γ} → ⟪ ⇧ (call Γ) ⟫ → ⟪ ⇧ (env Γ) ⟫ → ⟪ ⇧ (config Γ) ⟫
-- c ⟨,,⟩ ρ = [,,] ⋅ c ⋅ ρ
-- 
-- ↑steps⸢↯⸣ : ∀ {Γ} → ⟪ ⇧ (config Γ) ⇒ ⇧ (fset (⇧ (config Γ))) ⟫
-- ↑steps⸢↯⸣ {Γ} = witness-x (curry⸢λ↑⸣ id⸢λ↑⸣) $ mk[witness] fun ppr
--   where
--     fun : config Γ → fset (⇧ (config Γ))
--     fun ς = ↑⟨ map⸢list-set⸣ ↑ $ steps⸢↯⸣ ς ⟩
--     abstract
--       ppr : proper (_⊴_ ⇉ _⊴_) fun
--       ppr ↯ = xRx
-- 
-- η⸢ND⸣ : ∀ {𝓁} {A : POSet 𝓁} → ⟪ ⇧ (fset A) ⇒ 𝒫 A ⟫
-- η⸢ND⸣ {𝓁} {A} = witness-x (curry⸢λ↑⸣ id⸢ω⸣) $ mk[witness] fun ppr
--   where
--    fun : fset A → ⟪ A ⟫ → Set 𝓁
--    fun xs x = x ∈⸢fset⸣ xs
--    abstract
--      ppr : proper (_⊴_ ⇉ _⊵_ ⇉ [→]) fun
--      ppr {↑⟨ xs ⟩} {↑⟨ ys ⟩} ↑⟨ xs⊑ys ⟩ x⊵y (In {y'} x⊴y' y'∈xs) with xs⊑ys y'∈xs
--      ... | ∃ z ,, y'⊴z , z∈ys = In (y'⊴z ⌾ x⊴y' ⌾ x⊵y) z∈ys
-- 
-- γ⸢ND⸣ : ∀ {𝓁} {A : POSet 𝓁} → ⟪ 𝒫 A ⇒ 𝒫 (⇧ (fset A)) ⟫
-- γ⸢ND⸣ {𝓁} {A} = witness-x (curry⸢λ⸣ id⸢ω↑⸣) $ mk[witness] fun ppr
--   where
--     fun : ⟪ 𝒫 A ⟫ → fset A → Set 𝓁
--     fun X xs = ∀ {x} → x ∈⸢fset⸣ xs → x ⋿ X
--     abstract
--       ppr : proper (_⊑_ ⇉ _⊵_ ⇉ [→]) fun
--       ppr {X} {Y} X⊑Y {↑⟨ xs ⟩} {↑⟨ ys ⟩} ↑⟨ xs⊑ys ⟩ xs⊆X (In {y'} x⊴y' y'∈xs) with xs⊑ys y'∈xs
--       ... | ∃ z ,, y'⊴z , z∈xs = res-X-x[ω]⸢⊑⸣ X⊑Y (y'⊴z ⌾ x⊴y') $ xs⊆X $ In xRx z∈xs
-- 
-- sound⸢ND⸣ : ∀ {𝓁} {A : POSet 𝓁} {xs : ⟪ ⇧ (fset A) ⟫} → xs ⋿ γ⸢ND⸣ ⋅ (η⸢ND⸣ ⋅ xs)
-- sound⸢ND⸣ {xs = ↑⟨ xs ⟩} x∈xs = x∈xs
-- 
-- complete⸢ND⸣ : ∀ {𝓁} {A : POSet 𝓁} {X : ⟪ 𝒫 A ⟫} {xs : ⟪ ⇧ (fset A) ⟫} → xs ⋿ γ⸢ND⸣ ⋅ X → η⸢ND⸣ ⋅ xs ⊑ X
-- complete⸢ND⸣ {xs = ↑⟨ xs ⟩} xs⊑X = ext[ω]⸢⊑⸣ xs⊑X
-- 
-- pure⸢ND⸣ : ∀ {𝓁} {A B : POSet 𝓁} → ⟪ (A ⇒ ⇧ (fset B)) ⇒ (A ⇒ 𝒫 B) ⟫
-- pure⸢ND⸣ = [⊙] ⋅ η⸢ND⸣
-- 
-- β-steps⸢ext⸣ : ∀ {Γ} {ς ς' : ⟪ ⇧ (config Γ) ⟫} → ς' ⋿ ↑steps ⋅ ς ↔ ς' ⋿ pure⸢ND⸣ ⋅ ↑steps⸢↯⸣ ⋅ ς
-- β-steps⸢ext⸣ {Γ} {ς} {ς'} = LHS {Γ} {ς} {ς'} , RHS {Γ} {ς} {ς'}
--   where
--     LHS : ∀ {Γ} {ς ς' : ⟪ ⇧ (config Γ) ⟫} → ς' ⋿ ↑steps ⋅ ς → ς' ⋿ pure⸢ND⸣ ⋅ ↑steps⸢↯⸣ ⋅ ς
--     LHS {ς = ↑⟨ ⟨ Apply fa₁ fa₂ ka , ρ ⟩ ⟩} {↑⟨ ⟨ .c , .(ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣ [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣) ⟩ ⟩} (Apply {x} {k} {c} {ρ'} ⟦fa₁⟧ρ≡clo)
--       with ⟦ fa₁ ⟧ ρ | remember ⟦ fa₁ ⟧ ρ | decideDenote decideFClo ρ fa₁ 
--     ... | ⟦fa₁⟧ρ | Was ≡⟦fa₁⟧ρ | is[clo] rewrite ⟦fa₁⟧ρ≡clo with is[clo]
--     ... | Yes Is = In xRx Zero
--     ... | No not[clo] = exfalso $ not[clo] Is
--     LHS {ς = ↑⟨ ⟨ Call ka fa , ρ ⟩ ⟩} {↑⟨ ⟨ .c , .(ρ' [ x ↦ ⟦ fa ⟧ ρ ]⸢env⸣) ⟩ ⟩} (Call {x} {c} {ρ'} ⟦ka⟧ρ≡clo)
--       with ⟦ ka ⟧ ρ | remember ⟦ ka ⟧ ρ | decideDenote decideKClo ρ ka
--     ... | ⟦ka⟧ρ | Was ≡⟦ka⟧ρ | is[clo] rewrite ⟦ka⟧ρ≡clo with is[clo]
--     ... | Yes Is = In xRx Zero
--     ... | No not[clo] = exfalso $ not[clo] Is
--     RHS : ∀ {Γ} {ς ς' : ⟪ ⇧ (config Γ) ⟫} → ς' ⋿ pure⸢ND⸣ ⋅ ↑steps⸢↯⸣ ⋅ ς → ς' ⋿ ↑steps ⋅ ς
--     RHS {ς = ↑⟨ ⟨ Apply fa₁ fa₂ ka , ρ ⟩ ⟩} ς'∈steps[ς] with ⟦ fa₁ ⟧ ρ | remember ⟦ fa₁ ⟧ ρ | decideDenote decideFClo ρ fa₁ | ς'∈steps[ς]
--     ... | .(FClo x k c ρ') | Was ≡⟦fa₁⟧ρ | Yes (Is {x} {k} {c} {ρ'}) | In ↑⟨ ↯ ⟩ Zero = Apply $ ◇ ≡⟦fa₁⟧ρ
--     ... | ._ | Was ≡⟦fa₁⟧ρ | Yes Is | In ς'⊴ς'' (Suc ())
--     ... | ⟦fa₁⟧ρ | Was ≡⟦fa₁⟧ρ | No not[clo] | In _ ()
--     RHS {ς = ↑⟨ ⟨ Call ka fa , ρ ⟩ ⟩} ς'∈step[ς] = {!!}
-- 
-- β-steps⸢ext⸣' : ∀ {Γ} {ς ς' : ⟪ ⇧ (config Γ) ⟫} → ς' ⋿ ↑steps ⋅ ς ↔ ς' ⋿ pure⸢ND⸣ ⋅ ↑steps⸢↯⸣ ⋅ ς
-- β-steps⸢ext⸣' {ς = ↑⟨ ς ⟩} with steps⸢↯⸣-w/spec ς
-- ... | ∃ ςs ,, spec = {!!} , {!!}
-- 
-- -- config→prod : ∀ {Γ} → ⟪ ⇧ (config Γ) ⇒ ⇧ (call Γ) ⟨×⟩ ⇧ (env Γ) ⟫
-- -- config→prod {Γ} = witness-x (curry⸢λ↑⸣ id⸢λ↑⸣) $ mk[witness] fun ppr
-- --   where
-- --     fun : config Γ → prod (⇧ (call Γ)) (⇧ (env Γ))
-- --     fun ⟨ c , ρ ⟩ = ↑⟨ c ⟩ , ↑⟨ ρ ⟩
-- --     abstract
-- --       ppr : proper (_⊴_ ⇉ _⊴_) fun
-- --       ppr {⟨ c , ρ ⟩} ↯ = ↑⟨ ↯ ⟩ , ↑⟨ ↯ ⟩
-- -- 
-- -- β-steps[Apply] :
-- --   ∀ {Γ} {ρ : env Γ} {fa₁ fa₂ ka x k c ρ'}
-- --   → ⟦ fa₁ ⟧ ρ ≡ FClo x k c ρ'
-- --   → ↑steps ⋅ ↑ ⟨ Apply fa₁ fa₂ ka , ρ ⟩
-- --   ≈ return ⋅ (↑ ⟨ c , ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣ [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣ ⟩)
-- -- β-steps[Apply] {ρ = ρ} {fa₁} {fa₂} {ka} {x} {k} {c} {ρ'} ⟦fa₁⟧ρ≡clo = ext[ω]⸢≈⸣ $ LHS , RHS
-- --   where
-- --     LHS : ∀ {ς} → ς ⋿ ↑steps ⋅ ↑ ⟨ Apply fa₁ fa₂ ka , ρ ⟩ → ς ⋿ return ⋅ (↑ ⟨ c , ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣ [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣ ⟩)
-- --     LHS {↑⟨ ._ ⟩} (Apply ⟦fa₁⟧ρ≡clo') with ⟦fa₁⟧ρ≡clo ⌾ ◇ ⟦fa₁⟧ρ≡clo'
-- --     ... | ↯ = xRx
-- --     RHS : ∀ {ς} → ς ⋿ return ⋅ (↑ ⟨ c , ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣ [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣ ⟩) → ς ⋿ ↑steps ⋅ ↑ ⟨ Apply fa₁ fa₂ ka , ρ ⟩
-- --     RHS {↑⟨ .(⟨ c , ρ' [ k ↦ ⟦ ka ⟧ ρ ]⸢env⸣ [ x ↦ ⟦ fa₂ ⟧ ρ ]⸢env⸣ ⟩) ⟩} ↑⟨ ↯ ⟩ = Apply ⟦fa₁⟧ρ≡clo
-- -- 
-- -- β-steps[Apply]⸢∉⸣ :
-- --   ∀ {Γ} {ρ : env Γ} {fa₁ fa₂ ka}
-- --   → (∀ {x k c ρ'} → ⟦ fa₁ ⟧ ρ ≢ FClo x k c ρ')
-- --   → ↑steps ⋅ ↑ ⟨ Apply fa₁ fa₂ ka , ρ ⟩
-- --   ≈ ↑empty
-- -- β-steps[Apply]⸢∉⸣ {ρ = ρ} {fa₁} {fa₂} {ka} ⟦fa⟧ρ≢clo = ext[ω]⸢≈⸣ $ λ {ς} → LHS {ς} , RHS {ς}
-- --   where
-- --     LHS : ∀ {ς} → ς ⋿ ↑steps ⋅ ↑ ⟨ Apply fa₁ fa₂ ka , ρ ⟩ → ς ⋿ ↑empty
-- --     LHS {↑⟨ ⟨ c , ._ ⟩ ⟩} (Apply ⟦fa⟧ρ≡clo) = Lift $ ⟦fa⟧ρ≢clo ⟦fa⟧ρ≡clo
-- --     RHS : ∀ {ς} → ς ⋿ ↑empty → ς ⋿ ↑steps ⋅ ↑ ⟨ Apply fa₁ fa₂ ka , ρ ⟩
-- --     RHS (Lift ())
-- -- 
-- -- β-steps[Call] :
-- --   ∀ {Γ} {ρ : env Γ} {ka fa x c ρ'}
-- --   → ⟦ ka ⟧ ρ ≡ KClo x c ρ'
-- --   → ↑steps ⋅ ↑ ⟨ Call ka fa , ρ ⟩
-- --   ≈ return ⋅ (↑ ⟨ c , ρ' [ x ↦ ⟦ fa ⟧ ρ ]⸢env⸣ ⟩)
-- -- β-steps[Call] {ρ = ρ} {ka} {fa} {x} {c} {ρ'} ⟦ka⟧ρ≡clo = ext[ω]⸢≈⸣ $ LHS , RHS
-- --   where
-- --     LHS : ∀ {ς} → ς ⋿ ↑steps ⋅ ↑ ⟨ Call ka fa , ρ ⟩ → ς ⋿ return ⋅ (↑ ⟨ c , ρ' [ x ↦ ⟦ fa ⟧ ρ ]⸢env⸣ ⟩)
-- --     LHS {↑⟨ ._ ⟩} (Call ⟦ka⟧ρ≡clo') with ⟦ka⟧ρ≡clo ⌾ ◇ ⟦ka⟧ρ≡clo'
-- --     ... | ↯ = xRx
-- --     RHS : ∀ {ς} → ς ⋿ return ⋅ (↑ ⟨ c , ρ' [ x ↦ ⟦ fa ⟧ ρ ]⸢env⸣ ⟩) → ς ⋿ ↑steps ⋅ ↑ ⟨ Call ka fa , ρ ⟩
-- --     RHS {↑⟨ .(⟨ c , ρ' [ x ↦ ⟦ fa ⟧ ρ ]⸢env⸣ ⟩) ⟩} ↑⟨ ↯ ⟩ = Call ⟦ka⟧ρ≡clo
-- -- 
-- -- β-steps[Call]⸢∉⸣ :
-- --   ∀ {Γ} {ρ : env Γ} {ka fa}
-- --   → (∀ {x c ρ'} → ⟦ ka ⟧ ρ ≢ KClo x c ρ')
-- --   → ↑steps ⋅ ↑ ⟨ Call ka fa , ρ ⟩
-- --   ≈ ↑empty
-- -- β-steps[Call]⸢∉⸣ {ρ = ρ} {ka} {fa} ⟦ka⟧ρ≢clo = ext[ω]⸢≈⸣ $ λ {ς} → LHS {ς} , RHS {ς}
-- --   where
-- --     LHS : ∀ {ς} → ς ⋿ ↑steps ⋅ ↑ ⟨ Call ka fa  , ρ ⟩ → ς ⋿ ↑empty
-- --     LHS {↑⟨ ⟨ c , ._ ⟩ ⟩} (Call ⟦ka⟧ρ≡clo) = Lift $ ⟦ka⟧ρ≢clo ⟦ka⟧ρ≡clo
-- --     RHS : ∀ {ς} → ς ⋿ ↑empty → ς ⋿ ↑steps ⋅ ↑ ⟨ Call ka fa , ρ ⟩
-- --     RHS (Lift ())
-- -- 
