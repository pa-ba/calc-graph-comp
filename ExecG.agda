------------------------------------------------------------------------
-- Calculation of the graph-based machine execG for the language with
-- conditionals (see `Cond` module).
------------------------------------------------------------------------

module ExecG where

open import Data.Nat
open import Data.Bool
open import Data.List hiding (head)
open import Relation.Binary.PropositionalEquality hiding ([_])


--------------------------------
-- Tree-based target language --
--------------------------------

Stack : Set
Stack = List ℕ

-- For the calculation to work we have to add a constructor `FUN`

data Code : Set where
 PUSH : ℕ → Code → Code
 ADD : Code → Code
 JPZ : Code → Code → Code
 HALT : Code
 FUN : (Stack → Stack) → Code -- for calculating execᵍ



exec : Code → Stack → Stack
exec (PUSH n c) s = exec c (n ∷ s)
exec (ADD c) (n ∷ m ∷ s) = exec c ((m + n) ∷ s)
exec (JPZ c' c) (n ∷ s) = if n ≡ᵇ 0 then exec c' s else exec c s
exec HALT s = s
exec (FUN f) s = f s -- for calculating execᵍ
exec _ _ = []

---------------------------------
-- Graph-based target language --
---------------------------------

data Codeᵍ (l : Set) : Set where
  PUSHᵍ : ℕ → Codeᵍ l → Codeᵍ l
  ADDᵍ : Codeᵍ l → Codeᵍ l
  JPZᵍ : l → Codeᵍ l → Codeᵍ l
  HALTᵍ : Codeᵍ l
  JMPᵍ : l → Codeᵍ l
  LABᵍ : (l → Codeᵍ l) → Codeᵍ l → Codeᵍ l

⦅_⦆ : Codeᵍ Code → Code
⦅ PUSHᵍ n c ⦆ = PUSH n ⦅ c ⦆
⦅ ADDᵍ c ⦆ = ADD ⦅ c ⦆
⦅ JPZᵍ l c ⦆ = JPZ l ⦅ c ⦆
⦅ HALTᵍ ⦆ = HALT
⦅ JMPᵍ l ⦆ = l
⦅ LABᵍ f c ⦆ = ⦅ f ⦅ c ⦆ ⦆

-- By including `FUN` in `Code` we can implement a map function:
mapᵍ : ∀ {l l'} → (l → l') → (l' → l) → Codeᵍ l → Codeᵍ l'
mapᵍ f g (PUSHᵍ x c) = PUSHᵍ x (mapᵍ f g c)
mapᵍ f g (ADDᵍ c) = ADDᵍ (mapᵍ f g c)
mapᵍ f g (JPZᵍ x c) = JPZᵍ (f x) (mapᵍ f g c)
mapᵍ f g HALTᵍ = HALTᵍ
mapᵍ f g (JMPᵍ x) = JMPᵍ (f x)
mapᵍ f g (LABᵍ x c) = LABᵍ (λ l' → mapᵍ f g (x (g l'))) (mapᵍ f g c)


---------------------
-- calculate execᵍ --
---------------------

-- Calculated definition of execᵍ
execᵍ : Codeᵍ (Stack → Stack) → Stack → Stack
execᵍ (PUSHᵍ n c) s = execᵍ c (n ∷  s)
execᵍ (ADDᵍ c) (n ∷ m ∷ s) = execᵍ c (m + n ∷ s)
execᵍ (JPZᵍ l c) (n ∷ s) = if n ≡ᵇ 0 then l s else execᵍ c s
execᵍ HALTᵍ s = s
execᵍ (JMPᵍ l) s = l s
execᵍ (LABᵍ f c) s = execᵍ (f (execᵍ c)) s
execᵍ _ _ = []

-- we need function extensionality
postulate funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g


open ≡-Reasoning

-- calculation of execᵍ
spec-exec : ∀ (c : Codeᵍ (Stack → Stack)) {s} 
  → exec ⦅ mapᵍ FUN exec c ⦆ s ≡ execᵍ c s
spec-exec (PUSHᵍ n c) {s} = 
  exec ⦅ mapᵍ FUN exec (PUSHᵍ n c) ⦆ s 
  ≡⟨⟩ 
  exec (PUSH n ⦅ mapᵍ FUN exec c ⦆)  s 
  ≡⟨⟩ 
  exec ⦅ mapᵍ FUN exec c ⦆ (n ∷  s)
  ≡⟨ spec-exec c ⟩ 
  execᵍ c (n ∷  s)
  ∎
spec-exec (ADDᵍ c) {n ∷ m ∷ s} = 
  exec ⦅ ADDᵍ (mapᵍ FUN exec c) ⦆ (n ∷ m ∷ s)
  ≡⟨⟩
  exec ⦅ mapᵍ FUN exec c ⦆ (m + n ∷ s)
  ≡⟨ spec-exec c ⟩
  execᵍ c (m + n ∷ s)
  ∎
spec-exec (ADDᵍ c) {[]} = 
  exec ⦅ ADDᵍ (mapᵍ FUN exec c) ⦆ []
  ≡⟨⟩
  []
  ∎
spec-exec (ADDᵍ c) {n ∷ []} = 
  exec ⦅ ADDᵍ (mapᵍ FUN exec c) ⦆ (n ∷ [])
  ≡⟨⟩
  []
  ∎
spec-exec (JPZᵍ l c) {n ∷ s} = 
  exec ⦅ mapᵍ FUN exec (JPZᵍ l c) ⦆ (n ∷ s) 
  ≡⟨⟩
  (if n ≡ᵇ 0 then l s else exec ⦅ mapᵍ FUN exec c ⦆ s)
  ≡⟨ cong (λ h → if n ≡ᵇ 0 then l s else h) (spec-exec c) ⟩
  (if n ≡ᵇ 0 then l s else execᵍ c s)
  ∎
spec-exec (JPZᵍ l c) {[]} = 
  exec ⦅ mapᵍ FUN exec (JPZᵍ l c) ⦆ [] 
  ≡⟨⟩
  []
  ∎
spec-exec HALTᵍ {s} = 
    exec ⦅ mapᵍ FUN exec HALTᵍ ⦆ s 
    ≡⟨⟩
    s
    ∎
spec-exec (JMPᵍ l) {s} = 
    exec ⦅ mapᵍ FUN exec (JMPᵍ l)  ⦆ s 
    ≡⟨⟩
    l s 
    ∎
spec-exec (LABᵍ f c) {s} =
   exec ⦅ mapᵍ FUN exec (LABᵍ f c)  ⦆ s 
   ≡⟨⟩
   exec ⦅ mapᵍ FUN exec (f (exec ⦅ mapᵍ FUN exec c ⦆)) ⦆ s
   ≡⟨ spec-exec (f (exec ⦅ mapᵍ FUN exec c ⦆)) ⟩
   execᵍ (f (exec ⦅ mapᵍ FUN exec c ⦆)) s
   ≡⟨ cong (λ h → execᵍ (f h) s) (funext λ s → (spec-exec c) {s}) ⟩
   execᵍ (f (execᵍ c)) s
   ∎
