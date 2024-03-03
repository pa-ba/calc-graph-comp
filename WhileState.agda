{-# OPTIONS --sized-types #-}


------------------------------------------------------------------------
-- Calculation for a simple arithmetic expression language extended
-- with While loops and a reference cell (i.e. Put and Get opeators).
------------------------------------------------------------------------


module WhileState where

open import Code
open import Partial
open import Data.Nat
open import Data.Product
open import Data.Fin hiding (_+_)
open import Data.Fin.Patterns
open import Data.Bool
open import Data.List hiding (head)
open import Data.Vec hiding (_>>=_)
open import Relation.Binary.PropositionalEquality hiding ([_])

---------------------
-- Source language --
---------------------


data Expr : Set where
  Val : ℕ → Expr
  Add : Expr → Expr → Expr
  Put : Expr → Expr → Expr
  Get : Expr
  While : Expr → Expr → Expr

State : Set
State = ℕ

mutual
  eval : ∀ {i} → Expr → State → Partial (ℕ × State) i
  eval (Val n)     q = return (n , q)
  eval (Add x y)   q = do m , q1 ← eval x q ; n , q2 ← eval y q1 ; return (m + n , q2)
  eval Get         q = return (q , q)
  eval (Put x y)   q = do n , _ ← eval x q ; eval y n
  eval (While x y) q = do n , q1 ← eval x q
                          if n ≡ᵇ 0 then return (0 , q1)
                                    else do _ , q2 ← eval y q1 ; later (∞eval (While x y) q2)

  ∞eval : ∀ {i} → Expr → State → ∞Partial (ℕ × State) i
  force (∞eval x q) = eval x q


--------------------------------
-- Tree-based target language --
--------------------------------

data Instr : ℕ → Set where
 PUSH' : ℕ → Instr 0
 ADD' : Instr 0
 STORE' : Instr 0
 LOAD' : Instr 0
 POP' : Instr 0
 JPZ' : Instr 1


-- Constructors for `Code` type
pattern PUSH n c = PUSH' n ! ▸ c
pattern ADD c = ADD' ! ▸ c
pattern STORE c = STORE' ! ▸ c
pattern LOAD c = LOAD' ! ▸ c
pattern POP c = POP' ! ▸ c
pattern JPZ l c = JPZ' ! ＠ l ▸ c

Stack : Set
Stack = List ℕ

Conf : Set
Conf = Stack × State


mutual
  exec : ∀ {i} → Code Instr ∞ → Conf → Partial Conf i
  exec HALT       conf            = return conf
  exec (PUSH n c) (s , q)         = exec c (n ∷ s , q)
  exec (ADD c)    (m ∷ n ∷ s , q) = exec c ((n + m) ∷ s , q)
  exec (LOAD c)   (s , q)         = exec c (q ∷ s , q)
  exec (STORE c)  (n ∷ s , _)     = exec c (s , n)
  exec (REC c)    conf            = later (∞exec c conf)
  exec (POP c)    (_ ∷ s , q)     = exec c (s , q)
  exec (JPZ c' c) (n ∷ s , q)     = if n ≡ᵇ 0 then exec c' (0 ∷ s , q) else exec c (s , q)
  exec _          _               = return ([] , 0)

  ∞exec : ∀ {i} → ∞Code Instr ∞ → Conf → ∞Partial Conf i
  force (∞exec c x) = exec (cforce c) x


-------------------------
-- Tree-based compiler --
-------------------------

mutual
  comp : ∀ {i} → Expr → Code Instr i → Code Instr i
  comp (Val n)     c = PUSH n c
  comp (Add x y)   c = comp x (comp y (ADD c))
  comp Get         c = LOAD c
  comp (Put x y)   c = comp x (STORE (comp y c))
  comp (While x y) c = comp x (JPZ c (comp y (POP (REC (∞comp (While x y) c)))))
  
  ∞comp : ∀ {i} → Expr → Code Instr i → ∞Code Instr i
  cforce (∞comp x c) = comp x c


compile : ∀ {i} → Expr → Code Instr i
compile e = comp e HALT



ifzero-cong : ∀ {i A} {p1 p2 q1 q2 : Partial A ∞} n
  → p1 ~[ i ] q1 → p2 ~[ i ] q2
  → (if n ≡ᵇ 0 then p1 else p2) ~[ i ] (if n ≡ᵇ 0 then q1 else q2)
ifzero-cong zero b1 b2 = b1
ifzero-cong (suc n) b1 b2 = b2


----------------------------------------
-- Calculation of tree-based compiler --
----------------------------------------

module TreeComp where

  open ~i-Calculation

  -- specification and calculation of comp

  spec-comp : ∀ i x {s q c} →
    (do n , q' ← eval x q ; exec c (n ∷ s , q')) ~[ i ] exec (comp x c) (s , q)
  spec-comp zero _ =  ~izero
  spec-comp i (Val n) {s} {q} {c} =
    (do m , q' ← eval (Val n) q ; exec c (m ∷ s , q'))
    ≡⟨⟩
    (do exec c (n ∷ s , q))
    ≡⟨⟩
    (exec (PUSH n c) (s , q))
    ∎

  spec-comp i (Add x y) {s} {q} {c} =
    (do v , q' ← eval (Add x y) q ; exec c (v ∷ s , q'))
    ≡⟨⟩
    (do v , q' ← (do n , q1 ← eval x q
                     m , q2 ← eval y q1
                     return (n + m , q2))
        exec c (v ∷ s , q'))
    ~⟨  ~i>>=-assoc' (eval x q) (\ (n , q1) -> ~i>>=-assoc (eval y q1)) ⟩
    (do n , q1 ← eval x q
        m , q2 ← eval y q1
        exec c ((n + m) ∷ s , q2))
    ≡⟨⟩
    (do n , q1 ← eval x q
        m , q2 ← eval y q1
        exec (ADD c) (m ∷ n ∷ s , q2))
    ~⟨  ~i>>=-cong-r (eval x q) (λ _ → spec-comp i y)  ⟩
    (do n , q1 ← eval x q
        exec (comp y (ADD c)) (n ∷ s , q1))
    ~⟨ spec-comp i x ⟩
      exec (comp x (comp y (ADD c))) (s , q)
    ∎
    
  spec-comp i (Put x y) {s} {q} {c} =
    (do v , q' ← eval (Put x y) q ; exec c (v ∷ s , q'))
    ≡⟨⟩
    (do v , q' ← (do n , _ ← eval x q
                     eval y n)
        exec c (v ∷ s , q'))
    ~⟨ ~i>>=-assoc (eval x q) ⟩
    (do n , _ ← eval x q
        v , q' ← eval y n
        exec c (v ∷ s , q'))
    ~⟨ ~i>>=-cong-r (eval x q) (λ _ → spec-comp i y) ⟩
    (do n , _ ← eval x q
        exec (comp y c) (s , n))
    ≡⟨⟩
    (do n , q1 ← eval x q
        exec (STORE (comp y c)) (n ∷ s , q1))
    ~⟨ spec-comp i x ⟩
    exec (comp x (STORE (comp y c))) (s , q)
    ∎

  spec-comp i Get {s} {q} {c} =
    (do v , q' ← eval Get q ; exec c (v ∷ s , q'))
    ≡⟨⟩
    (do v , q' ← return (q , q)
        exec c (v ∷ s , q'))
    ≡⟨⟩
    exec c (q ∷ s , q)
    ≡⟨⟩
    exec (LOAD c) (s , q)
    ∎

  spec-comp i@(suc j) (While x y) {s} {q} {c} =
    (do v , q' ← eval (While x y) q ; exec c (v ∷ s , q'))
    ≡⟨⟩
    (do v , q' ← do n , q1 ← eval x q ; if n ≡ᵇ 0 then return (0 , q1) else do _ , q2 ← eval y q1 ; later (∞eval (While x y) q2)
        exec c (v ∷ s , q'))
    ~⟨ (~i>>=-assoc' (eval x q) λ { (zero , q) → ~irefl ; (suc n , q1) → ~i>>=-assoc (eval y q1)})⟩ 
    (do n , q1 ← eval x q
        if n ≡ᵇ 0 then exec c (0 ∷ s , q1) 
          else do _ , q2 ← eval y q1 ; later (∞eval (While x y) q2 ∞>>= λ (v , q') → exec c (v ∷ s , q')))
    ~⟨ (~i>>=-cong-r (eval x q) λ (n , q1) → ifzero-cong n ~irefl (~i>>=-cong-r (eval y q1) λ (_ , q2) → ~ilater (spec-comp j (While x y) {s} {q2} {c}))) ⟩
    (do n , q1 ← eval x q
        if n ≡ᵇ 0 then exec c (0 ∷ s , q1) 
          else do _ , q2 ← eval y q1 ; later (∞exec (∞comp (While x y) c) (s , q2)))
    ~⟨ (((~i>>=-cong-r (eval x q) λ { (zero , _) → ~irefl ; (suc n , q1) → ~i>>=-cong-r (eval y q1) λ _ → ~ilater ~irefl}))) ⟩
    (do n , q1 ← eval x q
        if n ≡ᵇ 0 then exec c (0 ∷ s , q1) else do _ , q2 ← eval y q1 ; exec (REC (∞comp (While x y) c)) (s , q2))
    ≡⟨⟩
    (do n , q1 ← eval x q
        if n ≡ᵇ 0 then exec c (0 ∷ s , q1) else do m , q2 ← eval y q1 ; exec (POP (REC (∞comp (While x y) c))) (m ∷ s , q2))
    ~⟨ ((~i>>=-cong-r (eval x q) λ { (zero , _) → ~irefl ; (suc n , q1) → spec-comp i y })) ⟩
    (do n , q1 ← eval x q
        if n ≡ᵇ 0 then exec c (0 ∷ s , q1) else do exec (comp y (POP (REC (∞comp (While x y) c)))) (s , q1))
    ~⟨ (((~i>>=-cong-r (eval x q) λ { (zero , _) → ~irefl ; (suc n , _) → ~irefl }))) ⟩
    (do n , q1 ← eval x q
        exec (JPZ c (comp y (POP (REC (∞comp (While x y) c))))) (n ∷ s , q1))
    ~⟨ spec-comp i x ⟩
    (exec (comp x (JPZ c (comp y (POP (REC (∞comp (While x y) c)))))) (s , q))
    ∎


  -- specification and calculation of compile

  spec-compile : ∀ i x {s q} →
    (do n , q' ← eval x q ; return (n ∷ s , q')) ~[ i ] exec (compile x) (s , q)
  spec-compile i x {s} {q} =
    (do n , q' ← eval x q ; return (n ∷ s , q')) 
    ≡⟨⟩
    (do n , q' ← eval x q ; exec HALT (n ∷ s , q')) 
    ~⟨ spec-comp i x ⟩ 
    exec (comp x HALT) (s , q)
    ∎

---------------------------------
-- Graph-based target language --
---------------------------------

-- Constructors for `Codeᵍ` type
pattern PUSHᵍ n c = PUSH' n ! ▸ᵍ c
pattern ADDᵍ c = ADD' ! ▸ᵍ c
pattern STOREᵍ c = STORE' ! ▸ᵍ c
pattern LOADᵍ c = LOAD' ! ▸ᵍ c
pattern POPᵍ c = POP' ! ▸ᵍ c
pattern JPZᵍ l c = JPZ' ! ＠ l ▸ᵍ c

execᵍ : ∀ {i} → (∀ {l} → Codeᵍ Instr l) → Conf → Partial Conf i
execᵍ c = exec ⦅ c ⦆


--------------------------
-- Graph-based compiler --
--------------------------

compᵍ : ∀ {i} → Expr → Codeᵍ Instr i → Codeᵍ Instr i
compᵍ (Val x) c = PUSHᵍ x c
compᵍ (Add x y) c = compᵍ x (compᵍ y ( ADDᵍ c ))
compᵍ (Put x y) c = compᵍ x (STOREᵍ (compᵍ y c))
compᵍ Get c = LOADᵍ c
compᵍ (While x y) c = LABᵍ← (λ l → compᵍ x (LABᵍ→ (λ l' → JPZᵍ l' (compᵍ y (POPᵍ (JMPᵍ l)))) c ))


compileᵍ : ∀ {i} → Expr → Codeᵍ Instr i
compileᵍ e = compᵍ e HALTᵍ

-- ≈ is a congruence for `comp`
mutual
  ≈comp : ∀ {i} {c d : Code Instr ∞} (x : Expr) → c ≈[ i ] d → comp x c ≈[ i ] comp x d
  ≈comp (Val x) b = ≈cong1 b
  ≈comp (Add x y) b = ≈comp x (≈comp y (≈cong1 b))
  ≈comp (Put x y) b = ≈comp x (≈cong1 (≈comp y b))
  ≈comp Get b = ≈cong1 b
  ≈comp {i} (While x y) b = ≈comp x (≈cong2 b (≈comp y (≈cong1 (≈REC (∞≈comp {i} _ b)))))

  ∞≈comp : ∀ {i} {c d : Code Instr ∞} (x : Expr) → c ≈[ i ] d → ∞comp x c ∞≈[ i ] ∞comp x d
  ≈force (∞≈comp x b) {j} = ≈comp {j} x (≈down b)


-----------------------------------------
-- Calculation of graph-based compiler --
-----------------------------------------

open ≈-Calculation

mutual

  -- specification and calculation of compᵍ

  spec-compᵍ : ∀ {i} x {c} → comp x ⦅ c ⦆ ≈[ i ] ⦅ compᵍ x c ⦆
  spec-compᵍ (Val x) {c} = 
    PUSH x ⦅ c ⦆
    ≡⟨⟩
    ⦅ PUSHᵍ x  c ⦆
   ∎
  
  spec-compᵍ (Add x y) {c} = 
    comp x (comp y (ADD ⦅ c ⦆))
    ≡⟨⟩
    comp x (comp y ⦅ ADDᵍ c ⦆)
    ≈⟨ ≈comp x (spec-compᵍ y) ⟩
    comp x ⦅ compᵍ y ( ADDᵍ c )⦆
    ≈⟨ spec-compᵍ x ⟩
    ⦅ compᵍ x (compᵍ y ( ADDᵍ c ))⦆ 
   ∎
  
  spec-compᵍ (Put x y) {c} = 
    comp x (STORE (comp y ⦅ c ⦆))
    ≈⟨ ≈comp x (≈cong1 (spec-compᵍ y)) ⟩
    comp x (STORE ⦅ compᵍ y c ⦆)
    ≡⟨⟩
    comp x ⦅ STOREᵍ (compᵍ y c)⦆
    ≈⟨ spec-compᵍ x ⟩
    ⦅ compᵍ x (STOREᵍ (compᵍ y c))⦆
   ∎

  spec-compᵍ Get {c} = 
    LOAD ⦅ c ⦆
    ≡⟨⟩
    ⦅ LOADᵍ c ⦆
   ∎
  
  spec-compᵍ {i} (While x y) {c} =
    comp x (JPZ ⦅ c ⦆ (comp y (POP (REC (∞comp (While x y) ⦅ c ⦆)))))
    ≈⟨ ≈comp x ((≈cong1 (≈comp y (≈cong1 (≈REC (∞spec-compᵍ {i} (While x y))))))) ⟩
    comp x (JPZ ⦅ c ⦆ (comp y (POP (REC ∞⦅ compᵍ (While x y) c ⦆))))
    ≡⟨⟩
    (λ l → comp x (JPZ ⦅ c ⦆ (comp y (POP l)))) (REC ∞⦅ compᵍ (While x y) c ⦆)
    ≡⟨⟩
    (λ l → comp x (JPZ ⦅ c ⦆ (comp y (POP ⦅ JMPᵍ l ⦆)))) (REC ∞⦅ compᵍ (While x y) c ⦆)
    ≡⟨⟩
    (λ l → comp x (JPZ ⦅ c ⦆ (comp y ⦅ POPᵍ (JMPᵍ l) ⦆))) (REC ∞⦅ compᵍ (While x y) c ⦆)
    ≈⟨ ≈comp x (≈cong1 (spec-compᵍ y)) ⟩
    (λ l → comp x (JPZ ⦅ c ⦆ ⦅ compᵍ y (POPᵍ (JMPᵍ l))⦆)) (REC ∞⦅ compᵍ (While x y) c ⦆)
    ≡⟨⟩
    (λ l → comp x ((λ l' → JPZ l' ⦅ compᵍ y (POPᵍ (JMPᵍ l))⦆) ⦅ c ⦆)) (REC ∞⦅ compᵍ (While x y) c ⦆)
    ≡⟨⟩
    (λ l → comp x ((λ l' → ⦅ JPZᵍ l' (compᵍ y (POPᵍ (JMPᵍ l))) ⦆) ⦅ c ⦆ )) (REC ∞⦅ compᵍ (While x y) c ⦆)
    ≡⟨⟩
    (λ l → comp x ⦅ LABᵍ→ (λ l' → JPZᵍ l' (compᵍ y (POPᵍ (JMPᵍ l)))) c ⦆) (REC ∞⦅ compᵍ (While x y) c ⦆)
    ≈⟨ spec-compᵍ x ⟩
    (λ l → ⦅ compᵍ x (LABᵍ→ (λ l' → JPZᵍ l' (compᵍ y (POPᵍ (JMPᵍ l)))) c )⦆) (REC ∞⦅ compᵍ (While x y) c ⦆)
    ≡⟨⟩
    ⦅ LABᵍ← (λ l → compᵍ x (LABᵍ→ (λ l' → JPZᵍ l' (compᵍ y (POPᵍ (JMPᵍ l)))) c ))⦆
   ∎
  
  ∞spec-compᵍ : ∀ {i} x {c} → ∞comp x ⦅ c ⦆ ∞≈[ i ] ∞⦅ compᵍ x c ⦆
  ≈force (∞spec-compᵍ x) = spec-compᵍ x


-- specification and calculation of compileᵍ

spec-compileᵍ : ∀ {i} x → compile x ≈[ i ] ⦅ compileᵍ x ⦆
spec-compileᵍ x =
  compile x
  ≡⟨⟩
  comp x HALT
  ≡⟨⟩
  comp x ⦅ HALTᵍ ⦆
  ≈⟨ spec-compᵍ x ⟩ 
  ⦅ compᵍ x HALTᵍ ⦆
  ∎
