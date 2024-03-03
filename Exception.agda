------------------------------------------------------------------------
-- Calculation for a simple arithmetic expression language with
-- exceptions.
------------------------------------------------------------------------

module Exception where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ([_])

----------------------
-- Pattern matching --
----------------------

-- definitions and lemmas for pattern matching on `Maybe`

match : ∀ {a b} {A : Set a} {B : Set b} → (x : Maybe A) → 
        ((x : A) → B) → B → B
match (just x) j n = j x
match nothing j n = n  


match-≡ : ∀ {a b} {A : Set a} {B : Set b} (x : Maybe A) {j1 j2 : A  → B} {n1 n2 : B} → 
        (∀ y → j1 y ≡ j2 y) → n1 ≡ n2 → match x j1 n1 ≡ match x j2 n2
match-≡ (just x) j n = j x
match-≡ nothing j n = n


match-match : ∀ {A B C : Set} (x : Maybe A) {j' : A → Maybe B} {j : B → C} {n' n} {j2 n2}
  → (∀ y → match (j' y) j n ≡ j2 y) → (match n' j n ≡ n2) → match (match x j' n') j n ≡ match x j2 n2
match-match (just x) jeq neq = jeq x
match-match nothing jeq neq = neq

---------------------
-- Source language --
---------------------

data Expr : Set where
  Val : ℕ → Expr
  Add : Expr → Expr → Expr
  Throw : Expr
  Catch : Expr → Expr → Expr


eval : Expr → Maybe ℕ
eval (Val n) = just n
eval (Add x y) = match (eval x) (λ n → match (eval y) (λ m → just (n + m)) nothing ) nothing
eval Throw = nothing
eval (Catch x y) = match (eval x) (λ n → just n) (eval y)


--------------------------------
-- Tree-based target language --
--------------------------------

data Code : Set where
  PUSH : ℕ → Code → Code
  ADD : Code → Code
  UNMARK : Code → Code
  MARK : Code → Code → Code
  THROW : Code
  HALT : Code


data Item : Set where
  VAL : ℕ → Item
  HAN : Code → Item

Stack : Set
Stack = List Item

mutual
  {-# TERMINATING #-}
  exec : Code → Stack → Stack
  exec (PUSH n c)  s = exec c (VAL n ∷ s)
  exec (ADD c) (VAL m ∷ VAL n ∷ t) = exec c (VAL (n + m) ∷ t)
  exec THROW s = fail s
  exec (MARK h c)  s = exec c (HAN h ∷ s)
  exec (UNMARK c)  (VAL n ∷ HAN _  ∷ t) = exec c (VAL n ∷ t)
  exec HALT        s = s
  exec _ s = []

  fail : Stack → Stack
  fail []           =  []
  fail (VAL _ ∷ s)  =  fail s
  fail (HAN h ∷ s)  =  exec h s


-------------------------
-- Tree-based compiler --
-------------------------

comp : Expr → Code → Code
comp (Val n)     c = PUSH n c
comp (Add x y)   c = comp x (comp y (ADD c))
comp Throw       c = THROW
comp (Catch x h) c = MARK (comp h c) (comp x (UNMARK c))


compile : Expr → Code
compile e = comp e HALT


----------------------------------------
-- Calculation of tree-based compiler --
----------------------------------------


open ≡-Reasoning

-- specification and calculation of comp

spec-comp : ∀ x {s c} →
    match (eval x) (λ n → exec c (VAL n ∷ s)) (fail s) ≡  exec (comp x c) s

spec-comp (Val n) {s} {c} =
    match (eval (Val n)) (λ n → exec c (VAL n ∷ s)) (fail s)
  ≡⟨⟩
    exec c (VAL n ∷ s)
  ≡⟨⟩
    exec (PUSH n c) s
  ∎

spec-comp (Add x y) {s} {c} = 
 match (match (eval x) (λ n → match (eval y) (λ m → just (n + m)) nothing) nothing)
      (λ n → exec c (VAL n ∷ s)) (fail s)
  ≡⟨ match-match (eval x) (λ n → match-match (eval y) (λ m → refl) refl) refl ⟩
 match (eval x) (λ n → match (eval y) (λ m → exec c (VAL (n + m) ∷ s)) (fail s)) (fail s)
  ≡⟨⟩
 match (eval x) (λ n → match (eval y) (λ m → exec (ADD c) (VAL m ∷ VAL n ∷ s)) (fail s)) (fail s)
  ≡⟨⟩
 match (eval x) (λ n → match (eval y) (λ m → exec (ADD c) (VAL m ∷ VAL n ∷ s)) (fail (VAL n ∷ s))) (fail s)
  ≡⟨ match-≡ (eval x) (λ n → spec-comp y) refl ⟩
 match (eval x) (λ n → exec (comp y (ADD c)) (VAL n ∷ s)) (fail s)
  ≡⟨ spec-comp x ⟩
 exec (comp x (comp y (ADD c))) s
  ∎
spec-comp Throw {s} {c} = 
  match (eval Throw) (λ n → exec c (VAL n ∷ s)) (fail s) 
   ≡⟨⟩  
  fail s
   ≡⟨⟩  
  exec THROW s
  ∎
spec-comp (Catch x y) {s} {c} = 
  match (eval (Catch x y)) (λ n → exec c (VAL n ∷ s)) (fail s) 
   ≡⟨⟩
  match (match (eval x) (λ n → just n) (eval y)) (λ n → exec c (VAL n ∷ s)) (fail s) 
   ≡⟨ match-match (eval x) (λ n → refl) refl ⟩
  match (eval x) (λ n → exec c (VAL n ∷ s)) (match (eval y) (λ n → exec c (VAL n ∷ s)) (fail s) )
   ≡⟨ match-≡ (eval x) (λ n → refl)  (spec-comp y) ⟩
  match (eval x) (λ n → exec c (VAL n ∷ s)) (exec (comp y c) s)
   ≡⟨⟩
  match (eval x) (λ n → exec c (VAL n ∷ s)) (fail (HAN (comp y c) ∷ s))
   ≡⟨⟩
  match (eval x) (λ n → exec (UNMARK c) (VAL n ∷ HAN (comp y c) ∷ s)) (fail (HAN (comp y c) ∷ s))
   ≡⟨ spec-comp x ⟩
  exec (comp x (UNMARK c)) (HAN (comp y c) ∷ s)
   ≡⟨⟩
  exec (MARK (comp y c) (comp x (UNMARK c))) s
  ∎

-- specification and calculation of compile

spec-compile : ∀ x {s} →
    match (eval x) (λ n → VAL n ∷ s) (fail s) ≡  exec (compile x) s
spec-compile x {s} = 
  match (eval x) (λ n → VAL n ∷ s) (fail s) 
  ≡⟨⟩ 
  match (eval x) (λ n → exec HALT (VAL n ∷ s)) (fail s) 
  ≡⟨ spec-comp x ⟩ 
  exec (comp x HALT) s
  ∎



---------------------------------
-- Graph-based target language --
---------------------------------

data Codeᵍ (l : Set) : Set where
  PUSHᵍ : ℕ → Codeᵍ l → Codeᵍ l
  ADDᵍ : Codeᵍ l → Codeᵍ l
  UNMARKᵍ : Codeᵍ l → Codeᵍ l
  MARKᵍ : l → Codeᵍ l → Codeᵍ l
  THROWᵍ : Codeᵍ l
  HALTᵍ : Codeᵍ l
  JMPᵍ : l → Codeᵍ l
  LABᵍ : (l → Codeᵍ l) → Codeᵍ l → Codeᵍ l

⦅_⦆ : Codeᵍ Code → Code
⦅ PUSHᵍ n c ⦆ = PUSH n ⦅ c ⦆
⦅ ADDᵍ c ⦆ = ADD ⦅ c ⦆
⦅ UNMARKᵍ c ⦆ = UNMARK ⦅ c ⦆
⦅ MARKᵍ l c ⦆ = MARK l ⦅ c ⦆
⦅ THROWᵍ ⦆ = THROW
⦅ HALTᵍ ⦆ = HALT
⦅ JMPᵍ l ⦆ = l
⦅ LABᵍ f c ⦆ = ⦅ f ⦅ c ⦆ ⦆

execᵍ : (∀ {l} → Codeᵍ l) → Stack → Stack
execᵍ c = exec ⦅ c ⦆


--------------------------
-- Graph-based compiler --
--------------------------

compᵍ : ∀ {l} → Expr → Codeᵍ l → Codeᵍ l
compᵍ (Val x) c = PUSHᵍ x c
compᵍ (Add x y) c = compᵍ x (compᵍ y ( ADDᵍ c ))
compᵍ Throw       c = THROWᵍ
compᵍ (Catch x y) c = LABᵍ (λ l → LABᵍ (λ l' → MARKᵍ l' (compᵍ x (UNMARKᵍ (JMPᵍ l)))) (compᵍ y (JMPᵍ l)) ) c

compileᵍ : Expr → (∀ {l} → Codeᵍ l)
compileᵍ e = compᵍ e HALTᵍ


-----------------------------------------
-- Calculation of graph-based compiler --
-----------------------------------------

-- specification and calculation of compᵍ

spec-compᵍ : ∀ x {c} → comp x ⦅ c ⦆ ≡ ⦅ compᵍ x c ⦆
spec-compᵍ (Val x) {c} = 
  begin
  (PUSH x ⦅ c ⦆)
  ≡⟨⟩
  (⦅ PUSHᵍ x c ⦆)
 ∎

spec-compᵍ (Add x y) {c} = 
  begin
  comp x (comp y (ADD ⦅ c ⦆))
  ≡⟨⟩
  comp x (comp y ( ⦅ ADDᵍ c ⦆))
  ≡⟨ cong (comp x) (spec-compᵍ y) ⟩
  comp x ⦅ compᵍ y ( ADDᵍ c )⦆
  ≡⟨ spec-compᵍ x ⟩
  ⦅ compᵍ x (compᵍ y ( ADDᵍ c ))⦆
 ∎
 
spec-compᵍ Throw {c} = 
  begin
  THROW
  ≡⟨⟩
  ⦅ THROWᵍ ⦆
 ∎
 
spec-compᵍ (Catch x y) {c} =
  begin
  MARK (comp y ⦅ c ⦆) (comp x (UNMARK ⦅ c ⦆))
  ≡⟨⟩
  (λ l → MARK (comp y l) (comp x (UNMARK l))) ⦅ c ⦆
  ≡⟨⟩
  (λ l → MARK (comp y ⦅ JMPᵍ l ⦆) (comp x (UNMARK ⦅ JMPᵍ l ⦆))) ⦅ c ⦆
  ≡⟨⟩
  (λ l → MARK (comp y ⦅ JMPᵍ l ⦆) (comp x ⦅ UNMARKᵍ (JMPᵍ l) ⦆)) ⦅ c ⦆
  ≡⟨ cong₂ MARK (spec-compᵍ y) (spec-compᵍ x) ⟩
  (λ l → MARK ⦅ compᵍ y (JMPᵍ l) ⦆ ⦅ compᵍ x (UNMARKᵍ (JMPᵍ l)) ⦆) ⦅ c ⦆
  ≡⟨⟩
  (λ l → (λ l' → MARK l' ⦅ compᵍ x (UNMARKᵍ (JMPᵍ l)) ⦆) ⦅ compᵍ y (JMPᵍ l) ⦆) ⦅ c ⦆
  ≡⟨⟩
  (λ l → (λ l' → ⦅ MARKᵍ l' (compᵍ x (UNMARKᵍ (JMPᵍ l))) ⦆) ⦅ compᵍ y (JMPᵍ l) ⦆) ⦅ c ⦆
  ≡⟨⟩
  (λ l → ⦅ LABᵍ (λ l' → MARKᵍ l' (compᵍ x (UNMARKᵍ (JMPᵍ l)))) (compᵍ y (JMPᵍ l)) ⦆ ) ⦅ c ⦆
  ≡⟨⟩
  ⦅ LABᵍ (λ l → LABᵍ (λ l' → MARKᵍ l' (compᵍ x (UNMARKᵍ (JMPᵍ l)))) (compᵍ y (JMPᵍ l)) ) c ⦆
 ∎
 

-- specification and calculation of compileᵍ

spec-compileᵍ : ∀ x → compile x ≡ ⦅ compileᵍ x ⦆
spec-compileᵍ x =
  compile x 
  ≡⟨ refl ⟩
  comp x HALT
  ≡⟨ refl ⟩
  comp x ⦅ HALTᵍ ⦆ 
  ≡⟨ spec-compᵍ x ⟩
  ⦅ compᵍ x HALTᵍ ⦆ 
  ∎