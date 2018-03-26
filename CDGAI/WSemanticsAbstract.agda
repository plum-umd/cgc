module CDGAI.WSemanticsAbstract where

open import Prelude
open import Poset
open import CDGAI.ZAbstraction
open import CDGAI.BoolAbstraction
open import CDGAI.EnvAbstraction
open import CDGAI.ASyntax
open import CDGAI.BSemantics
open import CDGAI.ASemantics
open import CDGAI.ASemanticsAbstract
open import CDGAI.BSemanticsAbstract
open import CDGAI.WSyntax
open import CDGAI.WSemantics

module _ {ℓ} {A B₁ B₂ : Poset ℓ} (⇄B⇄ : B₁ ⇄ᶜ B₂) where
  L1 : ∀ {x : ⟪ A ⟫} {y♯ : ⟪ B₂ ⟫} → (pure ⋅ ([,] ⋅ x)) *♮ ⋅ (γᶜ[ ⇄B⇄ ] ⋅ y♯) ≈♮ γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ ⟨ x ,♮ y♯ ⟩
  L1 {x} {y♯} = ext[℘]⸢≈⸣ $ λ {π} → ⟨ LHS {π} , RHS {π} ⟩
    where
      LHS : ∀ {π} → π ⋿ (pure ⋅ ([,] ⋅ x)) *♮ ⋅ (γᶜ[ ⇄B⇄ ] ⋅ y♯) → π ⋿ γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ ⟨ x ,♮ y♯ ⟩
      LHS {♮⟨ ⟨ x′ , y′ ⟩ ⟩} (∃℘ y ,, ⋿γ ,, ♮⟨ ⟨ ⊑ₓ , ⊑ʸ ⟩ ⟩) = ⟨ ⊑ₓ , res[x][℘]⸢⊑⸣ {X = γᶜ[ ⇄B⇄ ] ⋅ y♯} ⊑ʸ ⋿γ ⟩
      RHS : ∀ {π} → π ⋿ γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ ⟨ x ,♮ y♯ ⟩ → π ⋿ (pure ⋅ ([,] ⋅ x)) *♮ ⋅ (γᶜ[ ⇄B⇄ ] ⋅ y♯)
      RHS {♮⟨ ⟨ x′ , y′ ⟩ ⟩} ⟨ ⊑ₓ , ⋿γ ⟩ = ∃℘ y′ ,, ⋿γ ,, ♮⟨ ⟨ ⊑ₓ , xRx ⟩ ⟩

module _ {ℓ} {A B C : Poset ℓ} where
  L2 : ∀ {g : ⟪ A ↗ B ↗ ℘ C ⟫} {f : ⟪ A ↗ ℘ B ⟫} {X : ⟪ ℘ A ⟫}
    →  (apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ g ,♮ f ⟩ ∘♮ split♮) *♮ ⋅ X
    ⊑♮ (uncurry♮ ⋅ g) *♮ ⋅ (γ⸢IA⸣ ⋅ ⟨ X  ,♮ f *♮ ⋅ X ⟩)
  L2 {g} {f} {X} = ext[℘]⸢⊑⸣ P
    where
      P : ∀ {c : ⟪ C ⟫} → c ⋿ (apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ g ,♮ f ⟩ ∘♮ split♮) *♮ ⋅ X → c ⋿ (uncurry♮ ⋅ g) *♮ ⋅ (γ⸢IA⸣ ⋅ ⟨ X  ,♮ f *♮ ⋅ X ⟩)
      P (∃℘ x ,, ∈ₓ ,, ∃℘ y ,, ∈ʸ ,, ∈ᶜ) = ∃℘ ♮⟨ ⟨ x , y ⟩ ⟩ ,, ⟨ ∈ₓ , (∃℘ x ,, ∈ₓ ,, ∈ʸ) ⟩ ,, ∈ᶜ

module _ {ℓ} {A₁ A₂ B₁ B₂ : Poset ℓ} (⇄A⇄ : A₁ ⇄ᶜ A₂) (⇄B⇄ : B₁ ⇄ᶜ B₂) where
  L3 : ∀ {x♯ y♯} → γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄A⇄ ] ⋅ x♯ ,♮ γᶜ[ ⇄B⇄ ] ⋅ y♯ ⟩ ≈♮ γᶜ[ ⇄A⇄ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ ⟨ x♯ ,♮ y♯ ⟩
  L3 {x♯} {y♯} = ext[℘]⸢≈⸣ $ λ {xy} → ⟨ LHS {xy} , RHS {xy} ⟩
    where
      LHS : ∀ {xy} → xy ⋿ γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄A⇄ ] ⋅ x♯ ,♮ γᶜ[ ⇄B⇄ ] ⋅ y♯ ⟩ → xy ⋿ γᶜ[ ⇄A⇄ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ ⟨ x♯ ,♮ y♯ ⟩
      LHS {♮⟨ ⟨ x , y ⟩ ⟩} ⟨ ⋿ₓ , ⋿ʸ ⟩ = ⟨ ⋿ₓ , ⋿ʸ ⟩
      RHS : ∀ {xy} → xy ⋿ γᶜ[ ⇄A⇄ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ ⟨ x♯ ,♮ y♯ ⟩ → xy ⋿ γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄A⇄ ] ⋅ x♯ ,♮ γᶜ[ ⇄B⇄ ] ⋅ y♯ ⟩
      RHS {♮⟨ ⟨ x , y ⟩ ⟩} ⟨ ⋿ₓ , ⋿ʸ ⟩ = ⟨ ⋿ₓ , ⋿ʸ ⟩

module _ {ℓ} {A B C : Poset ℓ} where
  L4 : ∀ {f : ⟪ A ↗ B ↗ C ⟫} → uncurry♮ ⋅ (pure ∘♮ f) ≈♮ pure ⋅ (uncurry♮ ⋅ f)
  L4 {f} = ext[↗]⸢≈⸣ $ λ {xy} → ext[℘]⸢≈⸣ $ λ {z} → ⟨ LHS {xy} {z} , RHS {xy} {z} ⟩
    where
      LHS : ∀ {xy z} → z ⋿ uncurry♮ ⋅ (pure ∘♮ f) ⋅ xy → z ⋿ pure ⋅ (uncurry♮ ⋅ f) ⋅ xy
      LHS {♮⟨ ⟨ x , y ⟩ ⟩} ⋿₀ = ⋿₀
      RHS : ∀ {xy z} → z ⋿ pure ⋅ (uncurry♮ ⋅ f) ⋅ xy → z ⋿ uncurry♮ ⋅ (pure ∘♮ f) ⋅ xy
      RHS {♮⟨ ⟨ x , y ⟩ ⟩} ⋿₀ = ⋿₀

module _ {ℓ} {A B₁ B₂ : Poset ℓ} (⇄B⇄ : B₁ ⇄ᶜ B₂) where
  η[,] : ∀ (x : ⟪ A ⟫) (y : ⟪ B₁ ⟫) → ηᶜ[ id⸢⇄ᶜ⸣ {A = A} ∧⸢⇄ᶜ⸣ ⇄B⇄ ] ⋅ ⟨ x ,♮ y ⟩ ⊑♮ ⟨ x ,♮ ηᶜ[ ⇄B⇄ ] ⋅ y ⟩
  η[,] x y = xRx

  α[,] : ∀ (x : ⟪ A ⟫) → α[ ⇄B⇄ ↗⸢⇄ᶜ⸣ (id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄B⇄) ] ⋅ (pure ⋅ ([,] ⋅ x)) ⊑♮ pure ⋅ ([,] ⋅ x)
  α[,] x = π₂ ηηᶜ[ ⇄B⇄ , id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄B⇄ ] $ ext[↗]⸢⊑⸣ $ λ {y} → η[,] x y

module _ {Γ} where
  ⟦_⟧ʷ♯ : wexp Γ → ⟪ ⇧ (env♯ Γ) ↗ list♮ (⇧ (sexp Γ) ∧♮ ⇧ (env♯ Γ)) ⟫
  ⟦ Skip ⟧ʷ♯ = single♮ ∘♮ [,] ⋅ []ˢ♮
  ⟦ Assign x ae ⟧ʷ♯ =  apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ map[]♮ ∘♮ (([,] ⋅ []ˢ♮) ∘∘♮ extend♯[ x ]) ,♮ single♮ ∘♮ ⟦ ae ⟧ᵃ♯ ⟩ ∘♮ split♮
  ⟦ If be s₁ s₂ ⟧ʷ♯ = apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ if∘♯ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩) ,♮ ⟦ be ⟧ᵇ♯ ⟩ ∘♮ split♮
  ⟦ While be s ⟧ʷ♯ = apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ if∘♯ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮) ,♮ ⟦ be ⟧ᵇ♯ ⟩ ∘♮ split♮

  ⟦_⟧ˢ♯ : sexp Γ → ⟪ ⇧ (env♯ Γ) ↗ list♮ (⇧ (sexp Γ) ∧♮ ⇧ (env♯ Γ)) ⟫
  ⟦ [] ⟧ˢ♯ = const♮ ⋅ []♮
  ⟦ w ∷ s ⟧ˢ♯ = map[]♮ ⋅ (first♮ ⋅ (appendingˢ♮ ⋅ ♮⟨ s ⟩)) ∘♮ ⟦ w ⟧ʷ♯

  α⟦_⟧ʷ♯ : ∀ (w : wexp Γ) → α[ ⇄env⇄ ↗⸢⇄ᶜ⸣ (id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄) ] ⋅ ⟦ w ⟧ʷ ⊑♮ pure[]♮ ⋅ ⟦ w ⟧ʷ♯
  α⟦ Skip ⟧ʷ♯ = ext[↗]⸢⊑⸣ $ λ {ρ♯} → let open ProofMode[⊑] in [proof-mode]
    do [[ α[ ⇄env⇄ ↗⸢⇄ᶜ⸣ (id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄) ] ⋅ ⟦ Skip ⟧ʷ ⋅ ρ♯ ]]
     ‣ [[ αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (⟦ Skip ⟧ʷ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯)) ]]
     ‣ [focus-right [⋅] 𝑜𝑓 αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ] begin
       do [[ ⟦ Skip ⟧ʷ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
        ‣ [focus-left [⋅] 𝑜𝑓 (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ] begin
          do [[ ⟦ Skip ⟧ʷ *♮ ]]
          ‣ [focus-in [*] ] begin
            do [[ ⟦ Skip ⟧ʷ ]]
             ‣ ⟅ β[Skip] ⟆
             ‣ [[ pure ⋅ ([,] ⋅ []ˢ♮) ]]
            end
          ‣ [[ (pure ⋅ ([,] ⋅ []ˢ♮)) *♮ ]]
          end
        ‣ [[ (pure ⋅ ([,] ⋅ []ˢ♮)) *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
        ‣ ⟅ L1 ⇄env⇄ ⟆⸢≈⸣
        ‣ [[ γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] ⋅ ⟨ []ˢ♮ ,♮ ρ♯ ⟩ ]]
       end
     ‣ [[ αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] ⋅ ⟨ []ˢ♮ ,♮ ρ♯ ⟩) ]] 
     ‣ ⟅ reductiveᶜ[*][ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] ⟆
     ‣ [[ return♮ ⋅ ⟨ []ˢ♮ ,♮ ρ♯ ⟩ ]]
     ‣ ⟅ ◇ return[]/single ⟆⸢≈⸣
     ‣ [[ return[]♮ ⋅ (single♮ ⋅ ⟨ []ˢ♮ ,♮ ρ♯ ⟩) ]]
     ∎
  α⟦ Assign x ae ⟧ʷ♯ = ext[↗]⸢⊑⸣ $ λ {ρ♯} → let open ProofMode[⊑] in [proof-mode]
    do [[ α[ ⇄env⇄ ↗⸢⇄ᶜ⸣ (id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄) ] ⋅ ⟦ Assign x ae ⟧ʷ ⋅ ρ♯ ]]
     ‣ [[ αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (⟦ Assign x ae ⟧ʷ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯)) ]]
     ‣ [focus-right [⋅] 𝑜𝑓 αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ] begin
       do [[ ⟦ Assign x ae ⟧ʷ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
        ‣ [focus-left [⋅] 𝑜𝑓 γᶜ[ ⇄env⇄ ] ⋅ ρ♯ ] begin
          do [[ ⟦ Assign x ae ⟧ʷ *♮ ]]
           ‣ [focus-in [*] ] begin
             do [[ ⟦ Assign x ae ⟧ʷ ]]
              ‣ ⟅ β[Assign] ⟆
              ‣ [[ map℘♮ ⋅ ([,] ⋅ []ˢ♮) ∘♮ apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ extend♮[ x ] ,♮ ⟦ ae ⟧ᵃ♮ ⟩ ∘♮ split♮ ]]
             end
           ‣ [[ (map℘♮ ⋅ ([,] ⋅ []ˢ♮) ∘♮ apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ extend♮[ x ] ,♮ ⟦ ae ⟧ᵃ♮ ⟩ ∘♮ split♮) *♮ ]]
          end
        ‣ [[ (map℘♮ ⋅ ([,] ⋅ []ˢ♮) ∘♮ apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ extend♮[ x ] ,♮ ⟦ ae ⟧ᵃ♮ ⟩ ∘♮ split♮) *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
        ‣ [[ ((pure ⋅ ([,] ⋅ []ˢ♮)) *♮ ∘♮ apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ extend♮[ x ] ,♮ ⟦ ae ⟧ᵃ♮ ⟩ ∘♮ split♮) *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
        ‣ ⟅ associative[*] {g = pure ⋅ ([,] ⋅ []ˢ♮)} {f = apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ extend♮[ x ] ,♮ ⟦ ae ⟧ᵃ♮ ⟩ ∘♮ split♮} {X = (γᶜ[ ⇄env⇄ ] ⋅ ρ♯)} ⟆⸢≈⸣
        ‣ [[ (pure ⋅ ([,] ⋅ []ˢ♮)) *♮ ⋅ ((apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ extend♮[ x ] ,♮ ⟦ ae ⟧ᵃ♮ ⟩ ∘♮ split♮) *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯)) ]]
        ‣ [focus-right [⋅] 𝑜𝑓 (pure ⋅ ([,] ⋅ []ˢ♮)) *♮ ] begin
          do [[ (apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ extend♮[ x ] ,♮ ⟦ ae ⟧ᵃ♮ ⟩ ∘♮ split♮) *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
           ‣ ⟅ L2 {g = pure ∘♮ extend♮[ x ]} {f = ⟦ ae ⟧ᵃ♮} {X = γᶜ[ ⇄env⇄ ] ⋅ ρ♯} ⟆
           ‣ [[ (uncurry♮ ⋅ (pure ∘♮ extend♮[ x ])) *♮ ⋅ (γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄env⇄ ] ⋅ ρ♯ ,♮ ⟦ ae ⟧ᵃ♮ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ⟩) ]]
           ‣ [focus-right [⋅] 𝑜𝑓 (uncurry♮ ⋅ (pure ∘♮ extend♮[ x ])) *♮ ] begin
             do [focus-right [⋅] 𝑜𝑓 γ⸢IA⸣ ] $ [focus-right [,] 𝑜𝑓 γᶜ[ ⇄env⇄ ] ⋅ ρ♯ ] begin
               do [[ ⟦ ae ⟧ᵃ♮ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
                ‣ ⟅ π₁ γγᶜ[*][ ⇄env⇄ , ⇄ℤ⇄ ] (α[⟦⟧ᵃ] ae) ⟆
                ‣ [[ γᶜ[ ⇄ℤ⇄ ] *♮ ⋅ (pure ⋅ ⟦ ae ⟧ᵃ♯ ⋅ ρ♯) ]]
                ‣ ⟅ right-unit[*] ⟆⸢≈⸣
                ‣ [[ γᶜ[ ⇄ℤ⇄ ] ⋅ (⟦ ae ⟧ᵃ♯ ⋅ ρ♯) ]]
               end
             ‣ [[ γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄env⇄ ] ⋅ ρ♯ ,♮ γᶜ[ ⇄ℤ⇄ ] ⋅ (⟦ ae ⟧ᵃ♯ ⋅ ρ♯) ⟩ ]]
             ‣ ⟅ L3 ⇄env⇄ ⇄ℤ⇄ ⟆⸢≈⸣
             ‣ [[ γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟨ ρ♯ ,♮ ⟦ ae ⟧ᵃ♯ ⋅ ρ♯ ⟩ ]]
             end
          ‣ [[ (uncurry♮ ⋅ (pure ∘♮ extend♮[ x ])) *♮ ⋅ (γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟨ ρ♯ ,♮ ⟦ ae ⟧ᵃ♯ ⋅ ρ♯ ⟩) ]]
          ‣ [focus-left [*] 𝑜𝑓 γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟨ ρ♯ ,♮ ⟦ ae ⟧ᵃ♯ ⋅ ρ♯ ⟩ ] ⟅ L4 ⟆⸢≈⸣
          ‣ [[ (pure ⋅ (uncurry♮ ⋅ extend♮[ x ])) *♮ ⋅ (γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄ℤ⇄ ] ⋅ ⟨ ρ♯ ,♮ ⟦ ae ⟧ᵃ♯ ⋅ ρ♯ ⟩) ]]
          ‣ ⟅ π₁ (γγᶜ[*][ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄ℤ⇄ , ⇄env⇄ ] {f = pure ⋅ (uncurry♮ ⋅ extend♮[ x ])} {f♯ = pure ⋅ (uncurry♮ ⋅ extend♯[ x ])}) 
              (α[extend] {x = x}) {x = ⟨ ρ♯ ,♮ ⟦ ae ⟧ᵃ♯ ⋅ ρ♯ ⟩}
            ⟆
          ‣ [[ γᶜ[ ⇄env⇄ ] *♮ ⋅ (return♮ ⋅ (extend♯[ x ] ⋅ ρ♯ ⋅ (⟦ ae ⟧ᵃ♯ ⋅ ρ♯))) ]]
          ‣ ⟅ right-unit[*] ⟆⸢≈⸣
          ‣ [[ γᶜ[ ⇄env⇄ ] ⋅ (extend♯[ x ] ⋅ ρ♯ ⋅ (⟦ ae ⟧ᵃ♯ ⋅ ρ♯)) ]]
          end
        ‣ [[ (pure ⋅ ([,] ⋅ []ˢ♮)) *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ (extend♯[ x ] ⋅ ρ♯ ⋅ (⟦ ae ⟧ᵃ♯ ⋅ ρ♯))) ]]
        ‣ ⟅ L1 ⇄env⇄ ⟆⸢≈⸣
        ‣ [[ γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] ⋅ ⟨ []ˢ♮ ,♮ extend♯[ x ] ⋅ ρ♯ ⋅ (⟦ ae ⟧ᵃ♯ ⋅ ρ♯) ⟩ ]]
       end
     ‣ [[ αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] ⋅ ⟨ []ˢ♮ ,♮ extend♯[ x ] ⋅ ρ♯ ⋅ (⟦ ae ⟧ᵃ♯ ⋅ ρ♯) ⟩) ]]
     ‣ ⟅ reductiveᶜ[*][ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] ⟆
     ‣ [[ return♮ ⋅ ⟨ []ˢ♮ ,♮ extend♯[ x ] ⋅ ρ♯ ⋅ (⟦ ae ⟧ᵃ♯ ⋅ ρ♯) ⟩ ]]
     ‣ ⟅ ◇ return[]/single ⟆⸢≈⸣
     ‣ [[ return[]♮ ⋅ (single♮ ⋅ ⟨ []ˢ♮ ,♮ extend♯[ x ] ⋅ ρ♯ ⋅ (⟦ ae ⟧ᵃ♯ ⋅ ρ♯) ⟩) ]]
     ‣ [[ return[]♮ ⋅ (apply♮ ⋅ (apply⸢∧♮⸣ ⋅ ⟨ map[]♮ ∘♮ (([,] ⋅ []ˢ♮) ∘∘♮ extend♯[ x ]) ,♮ single♮ ∘♮ ⟦ ae ⟧ᵃ♯ ⟩ ⋅ ⟨ ρ♯ ,♮ ρ♯ ⟩)) ]]
     ∎
  α⟦ If be s₁ s₂ ⟧ʷ♯ = ext[↗]⸢⊑⸣ $ λ {ρ♯} → let open ProofMode[⊑] in [proof-mode]
    do [[ α[ ⇄env⇄ ↗⸢⇄ᶜ⸣ (id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄) ] ⋅ ⟦ If be s₁ s₂ ⟧ʷ ⋅ ρ♯ ]]
     ‣ [[ αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (⟦ If be s₁ s₂ ⟧ʷ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯)) ]]
     ‣ [focus-right [⋅] 𝑜𝑓 αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ] begin
       do [[ ⟦ If be s₁ s₂ ⟧ʷ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
        ‣ [focus-left [*] 𝑜𝑓 γᶜ[ ⇄env⇄ ] ⋅ ρ♯ ] begin
          do [[ ⟦ If be s₁ s₂ ⟧ʷ ]]
           ‣ ⟅ β[If] ⟆
           ‣ [[ apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ if∘♮ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩) ,♮ ⟦ be ⟧ᵇ ⟩ ∘♮ split♮ ]]
          end
        ‣ [[ (apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ if∘♮ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩) ,♮ ⟦ be ⟧ᵇ ⟩ ∘♮ split♮) *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
        ‣ ⟅ L2 {g = pure ∘♮ if∘♮ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩)} {f = ⟦ be ⟧ᵇ} {X = γᶜ[ ⇄env⇄ ] ⋅ ρ♯} ⟆
        ‣ [[ (uncurry♮ ⋅ (pure ∘♮ if∘♮ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩))) *♮ ⋅ (γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄env⇄ ] ⋅ ρ♯  ,♮ ⟦ be ⟧ᵇ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ⟩) ]]
        ‣ [focus-right [⋅] 𝑜𝑓 (uncurry♮ ⋅ (pure ∘♮ if∘♮ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩))) *♮ ] begin
          do [[ γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄env⇄ ] ⋅ ρ♯  ,♮ ⟦ be ⟧ᵇ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ⟩ ]]
           ‣ [focus-right [⋅] 𝑜𝑓 γ⸢IA⸣ ] $ [focus-right [,] 𝑜𝑓 γᶜ[ ⇄env⇄ ] ⋅ ρ♯ ] begin
             do [[ ⟦ be ⟧ᵇ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
              ‣ ⟅ π₁ (γγᶜ[*][ ⇄env⇄ , ⇄𝔹⇄ ] {f = ⟦ be ⟧ᵇ} {f♯ = pure ⋅ ⟦ be ⟧ᵇ♯}) (α[⟦⟧ᵇ] be) {x = ρ♯} ⟆
              ‣ [[ γᶜ[ ⇄𝔹⇄ ] *♮ ⋅ (pure ⋅ ⟦ be ⟧ᵇ♯ ⋅ ρ♯) ]]
              ‣ ⟅ right-unit[*] ⟆⸢≈⸣
              ‣ [[ γᶜ[ ⇄𝔹⇄ ] ⋅ (⟦ be ⟧ᵇ♯ ⋅ ρ♯) ]]
             end
           ‣ [[ γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄env⇄ ] ⋅ ρ♯  ,♮ γᶜ[ ⇄𝔹⇄ ] ⋅ (⟦ be ⟧ᵇ♯ ⋅ ρ♯) ⟩ ]]
           ‣ ⟅ L3 ⇄env⇄ ⇄𝔹⇄ ⟆⸢≈⸣
           ‣ [[ γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄ ] ⋅ ⟨ ρ♯  ,♮ ⟦ be ⟧ᵇ♯ ⋅ ρ♯ ⟩ ]]
          end
        ‣ [[ (uncurry♮ ⋅ (pure ∘♮ if∘♮ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩))) *♮ ⋅ (γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄ ] ⋅ ⟨ ρ♯  ,♮ ⟦ be ⟧ᵇ♯ ⋅ ρ♯ ⟩) ]]
        ‣ [focus-left [*] 𝑜𝑓 γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄ ] ⋅ ⟨ ρ♯  ,♮ ⟦ be ⟧ᵇ♯ ⋅ ρ♯ ⟩ ] ⟅ L4 ⟆⸢≈⸣
        ‣ [[ (pure ⋅ (uncurry♮ ⋅ (if∘♮ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩)))) *♮ ⋅ (γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄ ] ⋅ ⟨ ρ♯  ,♮ ⟦ be ⟧ᵇ♯ ⋅ ρ♯ ⟩) ]]
        ‣ ⟅ π₁ (γγᶜ[*][ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄ , id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ]
                {f = pure ⋅ (uncurry♮ ⋅ (if∘♮ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩)))}
                {f♯ = pure[]♮ ⋅ (uncurry♮ ⋅ (if∘♯ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩)))}) 
            (α[if∘] ⇄env⇄ (id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄) ([,] ⋅ ♮⟨ s₁ ⟩) ([,] ⋅ ♮⟨ s₂ ⟩) ([,] ⋅ ♮⟨ s₁ ⟩) ([,] ⋅ ♮⟨ s₂ ⟩) (α[,] ⇄env⇄ ♮⟨ s₁ ⟩) (α[,] ⇄env⇄ ♮⟨ s₂ ⟩))
            {x = ⟨ ρ♯ ,♮ ⟦ be ⟧ᵇ♯ ⋅ ρ♯ ⟩}
          ⟆
        ‣ [[ γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (return[]♮ ⋅ (if∘♯ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩) ⋅ ρ♯ ⋅ (⟦ be ⟧ᵇ♯ ⋅ ρ♯))) ]]
       end
     ‣ [[ αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (return[]♮ ⋅ (if∘♯ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩) ⋅ ρ♯ ⋅ (⟦ be ⟧ᵇ♯ ⋅ ρ♯)))) ]]
     ‣ ⟅ reductiveᶜ[⋅][ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] ⟆
     ‣ [[ return[]♮ ⋅ (if∘♯ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩) ⋅ ρ♯ ⋅ (⟦ be ⟧ᵇ♯ ⋅ ρ♯)) ]]
     ‣ [[ return[]♮ ⋅ (apply♮ ⋅ (apply⸢∧♮⸣ ⋅ ⟨ if∘♯ ⋅ ([,] ⋅ ♮⟨ s₁ ⟩) ⋅ ([,] ⋅ ♮⟨ s₂ ⟩) ,♮ ⟦ be ⟧ᵇ♯ ⟩ ⋅ (split♮ ⋅ ρ♯))) ]]
     ∎
  α⟦ While be s ⟧ʷ♯ = ext[↗]⸢⊑⸣ $ λ {ρ♯} → let open ProofMode[⊑] in [proof-mode]
    do [[ α[ ⇄env⇄ ↗⸢⇄ᶜ⸣ (id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄) ] ⋅ ⟦ While be s ⟧ʷ ⋅ ρ♯ ]]
     ‣ [[ αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (⟦ While be s ⟧ʷ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯)) ]]
     ‣ [focus-right [⋅] 𝑜𝑓 αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ] begin
       do [[ ⟦ While be s ⟧ʷ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
        ‣ [focus-left [*] 𝑜𝑓 γᶜ[ ⇄env⇄ ] ⋅ ρ♯ ] begin
          do [[ ⟦ While be s ⟧ʷ ]]
           ‣ ⟅ β[While] ⟆
           ‣ [[ apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ if∘♮ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮) ,♮ ⟦ be ⟧ᵇ ⟩ ∘♮ split♮ ]]
          end
        ‣ [[ (apply♮ ∘♮ apply⸢∧♮⸣ ⋅ ⟨ [*] ∘♮ pure ∘♮ if∘♮ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮) ,♮ ⟦ be ⟧ᵇ ⟩ ∘♮ split♮) *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
        ‣ ⟅ L2 {g = pure ∘♮ if∘♮ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮)} {f = ⟦ be ⟧ᵇ} {X = γᶜ[ ⇄env⇄ ] ⋅ ρ♯} ⟆
        ‣ [[ (uncurry♮ ⋅ (pure ∘♮ if∘♮ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮))) *♮ ⋅ (γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄env⇄ ] ⋅ ρ♯  ,♮ ⟦ be ⟧ᵇ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ⟩) ]]
        ‣ [focus-right [⋅] 𝑜𝑓 (uncurry♮ ⋅ (pure ∘♮ if∘♮ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮))) *♮ ] begin
          do [[ γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄env⇄ ] ⋅ ρ♯  ,♮ ⟦ be ⟧ᵇ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ⟩ ]]
           ‣ [focus-right [⋅] 𝑜𝑓 γ⸢IA⸣ ] $ [focus-right [,] 𝑜𝑓 γᶜ[ ⇄env⇄ ] ⋅ ρ♯ ] begin
             do [[ ⟦ be ⟧ᵇ *♮ ⋅ (γᶜ[ ⇄env⇄ ] ⋅ ρ♯) ]]
              ‣ ⟅ π₁ (γγᶜ[*][ ⇄env⇄ , ⇄𝔹⇄ ] {f = ⟦ be ⟧ᵇ} {f♯ = pure ⋅ ⟦ be ⟧ᵇ♯}) (α[⟦⟧ᵇ] be) {x = ρ♯} ⟆
              ‣ [[ γᶜ[ ⇄𝔹⇄ ] *♮ ⋅ (pure ⋅ ⟦ be ⟧ᵇ♯ ⋅ ρ♯) ]]
              ‣ ⟅ right-unit[*] ⟆⸢≈⸣
              ‣ [[ γᶜ[ ⇄𝔹⇄ ] ⋅ (⟦ be ⟧ᵇ♯ ⋅ ρ♯) ]]
             end
           ‣ [[ γ⸢IA⸣ ⋅ ⟨ γᶜ[ ⇄env⇄ ] ⋅ ρ♯  ,♮ γᶜ[ ⇄𝔹⇄ ] ⋅ (⟦ be ⟧ᵇ♯ ⋅ ρ♯) ⟩ ]]
           ‣ ⟅ L3 ⇄env⇄ ⇄𝔹⇄ ⟆⸢≈⸣
           ‣ [[ γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄ ] ⋅ ⟨ ρ♯  ,♮ ⟦ be ⟧ᵇ♯ ⋅ ρ♯ ⟩ ]]
          end
        ‣ [[ (uncurry♮ ⋅ (pure ∘♮ if∘♮ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮))) *♮ ⋅ (γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄ ] ⋅ ⟨ ρ♯  ,♮ ⟦ be ⟧ᵇ♯ ⋅ ρ♯ ⟩) ]]
        ‣ [focus-left [*] 𝑜𝑓 γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄ ] ⋅ ⟨ ρ♯  ,♮ ⟦ be ⟧ᵇ♯ ⋅ ρ♯ ⟩ ] ⟅ L4 ⟆⸢≈⸣
        ‣ [[ (pure ⋅ (uncurry♮ ⋅ (if∘♮ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮)))) *♮ ⋅ (γᶜ[ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄ ] ⋅ ⟨ ρ♯  ,♮ ⟦ be ⟧ᵇ♯ ⋅ ρ♯ ⟩) ]]
        ‣ ⟅ π₁ (γγᶜ[*][ ⇄env⇄ ∧⸢⇄ᶜ⸣ ⇄𝔹⇄ , id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ]
                {f = pure ⋅ (uncurry♮ ⋅ (if∘♮ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮)))}
                {f♯ = pure[]♮ ⋅ (uncurry♮ ⋅ (if∘♯ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮)))}) 
            (α[if∘] ⇄env⇄ (id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄)
                    ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ([,] ⋅ []ˢ♮)
                    ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ([,] ⋅ []ˢ♮)
                    (α[,] ⇄env⇄ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) (α[,] ⇄env⇄ []ˢ♮))
            {x = ⟨ ρ♯ ,♮ ⟦ be ⟧ᵇ♯ ⋅ ρ♯ ⟩}
          ⟆
        ‣ [[ γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (return[]♮ ⋅ (if∘♯ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮) ⋅ ρ♯ ⋅ (⟦ be ⟧ᵇ♯ ⋅ ρ♯))) ]]
       end
     ‣ [[ αᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (γᶜ[ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] *♮ ⋅ (return[]♮ ⋅ (if∘♯ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮) ⋅ ρ♯ ⋅ (⟦ be ⟧ᵇ♯ ⋅ ρ♯)))) ]]
     ‣ ⟅ reductiveᶜ[⋅][ id⸢⇄ᶜ⸣ ∧⸢⇄ᶜ⸣ ⇄env⇄ ] ⟆
     ‣ [[ return[]♮ ⋅ (if∘♯ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮) ⋅ ρ♯ ⋅ (⟦ be ⟧ᵇ♯ ⋅ ρ♯)) ]]
     ‣ [[ return[]♮ ⋅ (apply♮ ⋅ (apply⸢∧♮⸣ ⋅ ⟨ if∘♯ ⋅ ([,] ⋅ (♮⟨ s ⟩ ⧺ˢ♮ ♮⟨ While be s ∷ [] ⟩)) ⋅ ([,] ⋅ []ˢ♮) ,♮ ⟦ be ⟧ᵇ♯ ⟩ ⋅ (split♮ ⋅ ρ♯))) ]]
     ∎
