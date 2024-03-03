------------------------------------------------------------------------
-- Calculation for a simple arithmetic expression language extended
-- with if-then-else.
------------------------------------------------------------------------

module Cond where

open import Data.Nat
open import Data.Bool
open import Data.List hiding (head)
open import Relation.Binary.PropositionalEquality hiding ([_])



---------------------
-- Source language --
---------------------


data Expr : Set where
  Val : ℕ → Expr
  Add : Expr → Expr → Expr
  If : Expr → Expr → Expr → Expr

eval : Expr → ℕ
eval (Val n) = n
eval (Add x y) = eval x + eval y
eval (If x y z) = if eval x ≡ᵇ 0 then eval z else eval y

--------------------------------
-- Tree-based target language --
--------------------------------

Stack : Set
Stack = List ℕ

data Code : Set where
 HALT : Code
 PUSH : ℕ → Code → Code
 ADD : Code → Code
 JPZ : Code → Code → Code


exec : Code → Stack → Stack
exec HALT       s           = s
exec (PUSH n c) s           = exec c (n ∷ s)
exec (ADD c)    (n ∷ m ∷ s) = exec c ((m + n) ∷ s)
exec (JPZ c' c) (n ∷ s)     = if n ≡ᵇ 0 then exec c' s else exec c s
exec _           _          = []

-------------------------
-- Tree-based compiler --
-------------------------

comp : Expr → Code → Code
comp (Val n)    c = PUSH n c
comp (Add x y)  c = comp x (comp y (ADD c))
comp (If x y z) c = comp x (JPZ (comp z c) (comp y c))

compile : Expr → Code
compile e = comp e HALT


----------------------------------------
-- Calculation of tree-based compiler --
----------------------------------------


open ≡-Reasoning


-- specification and calculation of comp

spec-comp : ∀ x {s c} →
  exec c (eval x ∷ s) ≡  exec (comp x c) s
spec-comp (Val x) {s} {c} =
  exec c (eval (Val x) ∷ s)
  ≡⟨⟩
  (exec (PUSH x c) s)
  ∎
spec-comp (Add x y) {s} {c} =
  exec c (eval (Add x y) ∷ s)
  ≡⟨⟩
  exec c ((eval x + eval y) ∷ s)
  ≡⟨⟩
  exec (ADD c) (eval y ∷ eval x ∷ s)
  ≡⟨ spec-comp y ⟩
  exec (comp y (ADD c)) (eval x ∷ s)
  ≡⟨ spec-comp x ⟩
    exec (comp x (comp y (ADD c))) s
  ∎
  
spec-comp (If x y z) {s} {c} =
  exec c (eval (If x y z) ∷ s)
  ≡⟨⟩
  exec c ((if eval x ≡ᵇ 0 then eval z else eval y) ∷ s)
  ≡⟨ exec-if {c} ⟩
  (if eval x ≡ᵇ 0 then exec c (eval z ∷ s) else exec c (eval y ∷ s))
  ≡⟨ cong₂ (if_then_else_ (eval x ≡ᵇ 0)) (spec-comp z) (spec-comp y) ⟩
  (if eval x ≡ᵇ 0 then exec (comp z c) s else exec (comp y c) s)
  ≡⟨⟩
  (exec (JPZ (comp z c) (comp y c)) (eval x ∷ s))
  ≡⟨ spec-comp x ⟩
  (exec (comp x (JPZ (comp z c) (comp y c))) s)
  ∎
  where 
    exec-if : ∀ {c b x y s} → exec c ((if b then x else y) ∷ s) ≡ (if b then exec c (x ∷ s) else exec c (y ∷ s))
    exec-if {c} {false} = refl
    exec-if {c} {true} = refl

-- specification and calculation of compile

spec-compile : ∀ x {s} →
  eval x ∷ s ≡ exec (compile x) s
spec-compile x {s} = 
  eval x ∷ s
  ≡⟨⟩ 
  exec HALT (eval x ∷ s)
  ≡⟨ spec-comp x ⟩
  exec (comp x HALT) s
  ∎

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
⦅ HALTᵍ ⦆     = HALT
⦅ PUSHᵍ n c ⦆ = PUSH n ⦅ c ⦆
⦅ ADDᵍ c ⦆    = ADD ⦅ c ⦆
⦅ JPZᵍ l c ⦆  = JPZ l ⦅ c ⦆
⦅ JMPᵍ l ⦆    = l
⦅ LABᵍ f c ⦆  = ⦅ f ⦅ c ⦆ ⦆


--------------------------
-- Graph-based compiler --
--------------------------

compᵍ : ∀ {l} → Expr → Codeᵍ l → Codeᵍ l
compᵍ (Val x)    c = PUSHᵍ x c
compᵍ (Add x y)  c = compᵍ x (compᵍ y ( ADDᵍ c ))
compᵍ (If x y z) c = compᵍ x (LABᵍ (λ l → LABᵍ (λ l' → 
                        JPZᵍ l' (compᵍ y (JMPᵍ l))) (compᵍ z (JMPᵍ l))) c)

compileᵍ : Expr → (∀ {l} → Codeᵍ l)
compileᵍ e = compᵍ e HALTᵍ


-----------------------------------------
-- Calculation of graph-based compiler --
-----------------------------------------

-- specification and calculation of compᵍ

spec-compᵍ : ∀ x {c} → comp x ⦅ c ⦆ ≡ ⦅ compᵍ x c ⦆
spec-compᵍ (Val x) {c} = 
  (PUSH x ⦅ c ⦆)
  ≡⟨⟩
  ⦅ PUSHᵍ x c ⦆
  ∎
  
spec-compᵍ (Add x y) {c} = 
  comp x (comp y (ADD ⦅ c ⦆))
  ≡⟨⟩
  comp x (comp y ⦅ ADDᵍ c ⦆)
  ≡⟨ cong (comp x) (spec-compᵍ y) ⟩
  comp x ⦅ compᵍ y ( ADDᵍ c )⦆
  ≡⟨ spec-compᵍ x ⟩
  ⦅ compᵍ x (compᵍ y ( ADDᵍ c ))⦆
  ∎


spec-compᵍ (If x y z) {c} = 
  comp x (JPZ (comp z ⦅ c ⦆) (comp y ⦅ c ⦆))
  ≡⟨⟩
  comp x ((λ l → (JPZ (comp z l) (comp y l))) ⦅ c ⦆)
  ≡⟨⟩
  comp x ((λ l → (JPZ (comp z ⦅ JMPᵍ l ⦆) (comp y ⦅ JMPᵍ l ⦆))) ⦅ c ⦆)
  ≡⟨ cong₂ (λ h h' → comp x ((λ l → JPZ h h') ⦅ c ⦆)) (spec-compᵍ z) (spec-compᵍ y) ⟩
  comp x ((λ l → (JPZ ⦅ compᵍ z (JMPᵍ l) ⦆ ⦅ compᵍ y (JMPᵍ l) ⦆)) ⦅ c ⦆)
  ≡⟨⟩
  comp x ((λ l → (λ l' → (JPZ l' ⦅ compᵍ y (JMPᵍ l) ⦆)) ⦅ compᵍ z (JMPᵍ l) ⦆) ⦅ c ⦆)
  ≡⟨⟩
  comp x ((λ l → (λ l' → ⦅ JPZᵍ l' (compᵍ y (JMPᵍ l)) ⦆) ⦅ compᵍ z (JMPᵍ l) ⦆) ⦅ c ⦆)
  ≡⟨⟩
  comp x ((λ l → ⦅ LABᵍ (λ l' → JPZᵍ l' (compᵍ y (JMPᵍ l))) (compᵍ z (JMPᵍ l))⦆) ⦅ c ⦆)
  ≡⟨⟩
  (comp x ⦅ LABᵍ (λ l → LABᵍ (λ l' → JPZᵍ l' (compᵍ y (JMPᵍ l))) (compᵍ z (JMPᵍ l))) c ⦆)
  ≡⟨ spec-compᵍ x ⟩
  ⦅ compᵍ x (LABᵍ (λ l → (LABᵍ (λ l' → (JPZᵍ l' (compᵍ y (JMPᵍ l)))) (compᵍ z (JMPᵍ l)))) c) ⦆
  ∎
  
-- specification and calculation of compileᵍ

spec-compileᵍ : ∀ x → compile x ≡ ⦅ compileᵍ x ⦆
spec-compileᵍ x = 
  compile x 
  ≡⟨⟩
  comp x HALT
  ≡⟨⟩
  comp x HALT
  ≡⟨ spec-compᵍ x ⟩
  ⦅ compᵍ x HALTᵍ ⦆
  ∎