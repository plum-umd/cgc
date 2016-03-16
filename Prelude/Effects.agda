module Prelude.Effects where

open import Prelude.Core
open import Prelude.Classes
open import Prelude.Data.Lift
open import Prelude.Axioms

open Extensionality

-------------
-- Helpers --
-------------

_↝_ : ∀ {ℓ} → (Set ℓ → Set ℓ) → (Set ℓ → Set ℓ) → Set (↑ᴸ ℓ)
F ↝ G = ∀ {A} → F A → G A

record _↭_ {ℓ} (F : Set ℓ → Set ℓ) (G : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  field
    obs : F ↝ G
    eff : G ↝ F
    correct[obs/eff] : ∀ {A} (xF : F A) → eff (obs xF) ≡ xF
open _↭_ public

---------------------
-- Effect Functors --
---------------------

record reader-t {ℓ} (R : Set ℓ) (M : Set ℓ → Set ℓ) (A : Set ℓ) : Set ℓ where
  constructor mk[reader-t]
  field un[reader-t] : R → M A 
open reader-t public

run[reader-t] : ∀ {ℓ} {R} {M : Set ℓ → Set ℓ} {A} → R → reader-t R M A → M A
run[reader-t] r xM = un[reader-t] xM r

record writer-t {ℓ} (O : Set ℓ) (M : Set ℓ → Set ℓ) (A : Set ℓ) : Set ℓ where
  constructor mk[writer-t]
  field un[writer-t] : M (A ∧ O)
open writer-t public

record state-t {ℓ} (S : Set ℓ) (M : Set ℓ → Set ℓ) (A : Set ℓ) : Set ℓ where
  constructor mk[state-t]
  field un[state-t] : S → M (A ∧ S)
open state-t public

record failure-t {ℓ} (M : Set ℓ → Set ℓ) (A : Set ℓ) : Set ℓ where
  constructor mk[failure-t]
  field un[failure-t] : M (option A)
open failure-t public

record error-t {ℓ} (E : Set ℓ) (M : Set ℓ → Set ℓ) (A : Set ℓ) : Set ℓ  where
  constructor mk[error-t]
  field un[error-t] : M (E ∨ A)
open error-t public

record cont-t {ℓ} (B : Set ℓ) (M : Set ℓ → Set ℓ) (A : Set ℓ) : Set ℓ where
  constructor mk[cont-t]
  field un[cont-t] : (A → M B) → M B
open cont-t public

-----------------------
-- Effect Interfaces --
-----------------------

record Reader {ℓ} (R : Set ℓ) (M : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  field reader : M ↭ reader-t R M
  reader/obs : M ↝ reader-t R M
  reader/obs = obs reader
  reader/eff : reader-t R M ↝ M
  reader/eff = eff reader
  ask : ∀ {{_ : Monad M}} → M R
  ask = reader/eff (mk[reader-t] return)
  local-env : ∀ {A} → R → M A → M A
  local-env r xM = un[reader-t] (reader/obs xM) r
open Reader {{...}} public

record Writer {ℓ} (O : Set ℓ) (M : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  field writer : M ↭ writer-t O M
  writer/obs : M ↝ writer-t O M
  writer/obs = obs writer
  writer/eff : writer-t O M ↝ M
  writer/eff = eff writer
  tell : ∀ {{_ : Monad M}} → O → M (lift ℓ unit)
  tell o = writer/eff (mk[writer-t] (return (mk[lift] tt , o)))
  hijack : ∀ {A} → M A → M (A ∧ O)
  hijack xM = un[writer-t] (writer/obs xM)
open Writer {{...}} public

record State {ℓ} (S : Set ℓ) (M : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  field state : M ↭ state-t S M
  state/obs : M ↝ state-t S M
  state/obs = obs state
  state/eff : state-t S M ↝ M
  state/eff = eff state
  get : ∀ {{_ : Monad M}} → M S
  get = state/eff (mk[state-t] (λ s → return (s , s)))
  put : ∀ {{_ : Monad M}} → S → M (lift ℓ unit)
  put s = state/eff (mk[state-t] (λ _ → return (mk[lift] tt , s)))
  local-state : ∀ {A} → S → M A → M (A ∧ S)
  local-state s xM = un[state-t] (state/obs xM) s
open State {{...}} public

record Failure {ℓ} (M : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  field failure : M ↭ failure-t M
  failure/obs : M ↝ failure-t M
  failure/obs = obs failure
  failure/eff : failure-t M ↝ M
  failure/eff = eff failure
  fail : ∀ {{_ : Monad M}} {A} → M A
  fail = failure/eff (mk[failure-t] (return None))
  try : ∀ {{_ : Monad M}} {A} → M A → M A → M A
  try xM₁ xM₂ =
    do xO ← un[failure-t] (failure/obs xM₁)
     ‣ case xO 𝑜𝑓 λ
       { None → xM₂
       ; (Some x) → return x
       }
open Failure {{...}} public

record Error {ℓ} (E : Set ℓ) (M : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  field error : M ↭ error-t E M
  error/obs : M ↝ error-t E M
  error/obs = obs error
  error/eff : error-t E M ↝ M
  error/eff = eff error
  throw : ∀ {{_ : Monad M}} {A} → E → M A
  throw e = error/eff (mk[error-t] (return (Inl e)))
  catch : ∀ {{_ : Monad M}} {A} → M A → (E → M A) → M A
  catch xM f =
    do xO ← un[error-t] (error/obs xM)
     ‣ case xO 𝑜𝑓 λ
       { (Inl e) → f e
       ; (Inr x) → return x
       }
open Error {{...}} public

record Cont {ℓ} (B : Set ℓ) (M : Set ℓ → Set ℓ) : Set (↑ᴸ ℓ) where
  field cont : M ↭ cont-t B M
  cont/obs : M ↝ cont-t B M
  cont/obs = obs cont
  cont/eff : cont-t B M ↝ M
  cont/eff = eff cont
  callcc : ∀ {A} → ((A → M B) → M B) → M A
  callcc f = cont/eff (mk[cont-t] f)
  withc : ∀ {A} → (A → M B) → M A → M B
  withc f xM = un[cont-t] (cont/obs xM) f
open Cont {{...}} public

---------------
-- Instances --
---------------

module _ {ℓ} {R} {M : Set ℓ → Set ℓ} where
  reader/obs⸢reader-t⸣ : reader-t R M ↝ reader-t R (reader-t R M)
  reader/obs⸢reader-t⸣ = (λ f → mk[reader-t] $ mk[reader-t] ∘ f) ∘ ff ∘ un[reader-t]
    where
      ff : ∀ {A} → (R → M A) → R → R → M A
      ff f r₁ r₂ = f r₁
  reader/eff⸢reader-t⸣ : reader-t R (reader-t R M) ↝ reader-t R M
  reader/eff⸢reader-t⸣ = mk[reader-t] ∘ ff ∘ (λ xMM → un[reader-t] ∘ un[reader-t] xMM)
    where
      ff : ∀ {A} → (R → R → M A) → R → M A
      ff f r = f r r
  reader/correct⸢reader-t⸣ : ∀ {A} (xM : reader-t R M A) → (reader/eff⸢reader-t⸣ ∘ reader/obs⸢reader-t⸣) xM ≡ xM
  reader/correct⸢reader-t⸣ xM = ↯
  instance
    Reader[reader-t] : Reader R (reader-t R M)
    Reader[reader-t] = record
      { reader = record
          { obs = reader/obs⸢reader-t⸣
          ; eff = reader/eff⸢reader-t⸣
          ; correct[obs/eff] = reader/correct⸢reader-t⸣
          }
      }

module _ {ℓ} {O} {{_ : Monoid O}} {M : Set ℓ → Set ℓ} {{_ : Functor M}} where
  writer/obs⸢writer-t⸣ : writer-t O M ↝ writer-t O (writer-t O M)
  writer/obs⸢writer-t⸣ = mk[writer-t] ∘ mk[writer-t] ∘ map ff ∘ un[writer-t]
    where
      ff : ∀ {A} → A ∧ O → (A ∧ O) ∧ O
      ff xo = xo , null
  writer/eff⸢writer-t⸣ : writer-t O (writer-t O M) ↝ writer-t O M
  writer/eff⸢writer-t⸣ = mk[writer-t] ∘ map ff ∘ un[writer-t] ∘ un[writer-t]
    where
      ff : ∀ {A} → (A ∧ O) ∧ O → A ∧ O
      ff ((x , o₁) , o₂) = (x , o₁ ⧺ o₂)
  writer/correct⸢writer-t⸣ : ∀ {A} (xM : writer-t O M A) → (writer/eff⸢writer-t⸣ ∘ writer/obs⸢writer-t⸣) xM ≡ xM
  writer/correct⸢writer-t⸣ (mk[writer-t] xOM) =
    res[•x][ mk[writer-t] ] $
      unit[map] xOM
      ⊚ ( res[•x•][ map , xOM ] $ ext[≡] _ id $ λ
            { (x , o) → res[••y][ _,_ , x ] $ right-unit[⧺] o
            } )
      ⊚ ◇ (homomorphic[map] _ _ xOM)
  instance
    Writer[writer-t] : Writer O (writer-t O M)
    Writer[writer-t] = record
      { writer = record
          { obs = writer/obs⸢writer-t⸣
          ; eff = writer/eff⸢writer-t⸣
          ; correct[obs/eff] = writer/correct⸢writer-t⸣
          }
      }

---------------
-- Commuting --
---------------

module _ {ℓ} {M : Set ℓ → Set ℓ} {{_ : Functor M}} where
  failure/obs⸢failure-t⸣ : failure-t M ↝ failure-t (failure-t M)
  failure/obs⸢failure-t⸣ = mk[failure-t] ∘ mk[failure-t] ∘ map ff ∘ un[failure-t]
    where
      ff : ∀ {A} → option A → option (option A)
      ff xO = Some xO
  failure/eff⸢failure-t⸣ : failure-t (failure-t M) ↝ failure-t M
  failure/eff⸢failure-t⸣ = mk[failure-t] ∘ map ff ∘ un[failure-t] ∘ un[failure-t]
    where
      ff : ∀ {A} → option (option A) → option A
      ff None = None
      ff (Some None) = None
      ff (Some (Some x)) = Some x
  failure/correct⸢failure-t⸣ : ∀ {A} (xM : failure-t M A) → (failure/eff⸢failure-t⸣ ∘ failure/obs⸢failure-t⸣) xM ≡ xM
  failure/correct⸢failure-t⸣ (mk[failure-t] xOM) =
    res[•x][ mk[failure-t] ] $
      unit[map] xOM
      ⊚ ( res[•x•][ map , xOM ] $ ext[≡] _ id $ λ
            { None → ↯
            ; (Some x) → ↯
            } )
      ⊚ ◇ (homomorphic[map] _ _ xOM)
  instance
    Failure[failure-t] : Failure (failure-t M)
    Failure[failure-t] = record
      { failure = record
          { obs = failure/obs⸢failure-t⸣
          ; eff = failure/eff⸢failure-t⸣
          ; correct[obs/eff] = failure/correct⸢failure-t⸣
          }
      }

module _ {ℓ} {O} {{_ : Monoid O}} {M : Set ℓ → Set ℓ} {{_ : Functor M}} where
  comm/writer/failure : writer-t O (failure-t M) ↝ failure-t (writer-t O M)
  comm/writer/failure = mk[failure-t] ∘ mk[writer-t] ∘ map ff ∘ un[failure-t] ∘ un[writer-t]
    where
      ff : ∀ {A} → option (A ∧ O) → option A ∧ O
      ff None = None , null
      ff (Some (x , o)) = (Some x , o)
  comm/failure/writer : failure-t (writer-t O M) ↝ writer-t O (failure-t M)
  comm/failure/writer = mk[writer-t] ∘ mk[failure-t] ∘ map ff ∘ un[writer-t] ∘ un[failure-t]
    where
      ff : ∀ {A} → option A ∧ O → option (A ∧ O)
      ff (None , _) = None
      ff (Some x , o) = Some (x , o)
  correct/comm/writer/failure : ∀ {A} (xM : writer-t O (failure-t M) A) → (comm/failure/writer ∘ comm/writer/failure) xM ≡ xM
  correct/comm/writer/failure (mk[writer-t] (mk[failure-t] xOOM)) =
    res[•x][ mk[writer-t] ∘ mk[failure-t] ] $
      unit[map] xOOM
      ⊚ ( res[•x•][ map , xOOM ] $ ext[≡] _ id $ λ
            { None → ↯
            ; (Some x) → ↯
            } )
      ⊚ ◇ (homomorphic[map] _ _ xOOM)
