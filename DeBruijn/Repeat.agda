{-# OPTIONS --sized-types #-}

------------------------------------------------------------------------
-- Calculation for a simple arithmetic expression language extended
-- with (degenerate) loops.
------------------------------------------------------------------------

module DeBruijn.Repeat where

open import DeBruijn.Code
open import Partial
open import Data.Nat
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
  Repeat : Expr → Expr

mutual
  eval : ∀ {i} → Expr → Partial ℕ i
  eval (Val x) = return x
  eval (Add x y) =
    do n ← eval x
       m ← eval y
       return (n + m)
  eval (Repeat x) = eval x >> later (∞eval (Repeat x))

  ∞eval : ∀ {i} → Expr → ∞Partial ℕ i
  force (∞eval x) = eval x

--------------------------------
-- Tree-based target language --
--------------------------------

data Instr : ℕ → Set where
 PUSH' : ℕ → Instr 0
 ADD' : Instr 0
 POP' : Instr 0
 
-- Constructors for `Code` type
pattern PUSH n c = PUSH' n ! ▸ c
pattern ADD c = ADD' ! ▸ c
pattern POP c = POP' ! ▸ c

Stack : Set
Stack = List ℕ


mutual
  exec : ∀ {i} → Code Instr ∞ → Stack → Partial Stack i
  exec (PUSH n c) s           = exec c (n ∷ s)
  exec (ADD c)    (m ∷ n ∷ s) = exec c ((n + m) ∷ s)
  exec (POP c)    (_ ∷ s)     = exec c s
  exec (REC c)    s           = later (∞exec' c s)
  exec HALT       s           = return s
  exec _          _           = return []

  ∞exec : ∀ {i} → Code Instr ∞ → Stack → ∞Partial Stack i
  force (∞exec e x) = exec e x

  ∞exec' : ∀ {i} → ∞Code Instr ∞ → Stack → ∞Partial Stack i
  force (∞exec' c x) = exec (cforce c) x


-------------------------
-- Tree-based compiler --
-------------------------

mutual
  comp : ∀ {i} → Expr → Code Instr i → Code Instr i
  comp (Val n)    c = PUSH n c
  comp (Add x y)  c = comp x (comp y (ADD c))
  comp (Repeat x) c = comp x (POP (REC (∞comp (Repeat x) c)))

  ∞comp : ∀ {i} → Expr → Code Instr i → ∞Code Instr i
  cforce (∞comp x c) = comp x c



compile : ∀ {i} → Expr → Code Instr i
compile e = comp e HALT


----------------------------------------
-- Calculation of tree-based compiler --
----------------------------------------

module TreeComp where

  open ~i-Calculation

  -- specification and calculation of comp

  spec-comp : ∀ i x {s c} →
    (do v ← eval x
        exec c (v ∷ s))
    ~[ i ]
    (exec (comp x c) s)
  spec-comp zero _ =  ~izero
  spec-comp i (Val x) {s} {c} =
    (eval (Val x) >>= (λ v → exec c (v ∷ s)))
    ≡⟨⟩
    (exec (PUSH x c) s)
    ∎
  spec-comp i (Add x y) {s} {c} =
    (eval (Add x y) >>= (\ v → exec c (v ∷ s)))
    ≡⟨⟩
    (do v <- (do n ← eval x
                 m ← eval y
                 return (n + m))
        exec c (v ∷ s))
    ~⟨  ~i>>=-assoc (eval x) ⟩
    (do n ← eval x
        v <- (do m ← eval y
                 return (n + m))
        exec c (v ∷ s))
    ~⟨  ~i>>=-cong-r (eval x) (\ n -> ~i>>=-assoc (eval y)) ⟩
    (do n ← eval x
        m ← eval y
        v <- (return (n + m))
        exec c (v ∷ s))
    ≡⟨⟩
    (do n ← eval x
        m ← eval y
        exec c ((n + m) ∷ s))
    ≡⟨⟩
    (do n ← eval x
        m ← eval y
        exec (ADD c) (m ∷ n ∷ s))
    ~⟨  ~i>>=-cong-r (eval x) (\ n' → spec-comp i  y)  ⟩
    (do n ← eval x
        exec (comp y (ADD c)) (n ∷ s))
    ~⟨ spec-comp i x ⟩
      exec (comp x (comp y (ADD c))) s
    ∎
    
  spec-comp i@(suc j) (Repeat x) {s} {c} =
      (do v ← eval (Repeat x) ; exec c (v ∷ s))
    ≡⟨⟩
      (do v ← do eval x ; later (∞eval (Repeat x))
          exec c (v ∷ s))
    ~⟨ ~i>>=-assoc (eval x) ⟩ 
      (do eval x ; later (∞eval (Repeat x) ∞>>= λ m → exec c (m ∷ s)))
    ~⟨ (~i>>=-cong-r (eval x) λ _ → ~ilater (spec-comp j (Repeat x) {s} {c})) ⟩
      (do eval x ; later (∞exec (comp (Repeat x) c) s))
    ~⟨ ~i>>=-cong-r (eval x) (λ _ → ~ilater ~irefl) ⟩
    (do eval x ; exec (REC (∞comp (Repeat x) c)) s)
    ≡⟨⟩
    (do m ← eval x ; exec (POP (REC (∞comp (Repeat x) c))) (m ∷ s))
    ~⟨ spec-comp i x ⟩
    (exec (comp x (POP (REC (∞comp (Repeat x) c)))) s)
    ∎

  -- specification and calculation of compile

  spec-compile : ∀ i x {s} →
    (do v ← eval x ; return (v ∷ s))  ~[ i ] exec (compile x) s
  spec-compile i x {s} = 
    (do v ← eval x ; return (v ∷ s))
    ≡⟨⟩ 
    (do v ← eval x ; exec HALT (v ∷ s))
    ~⟨ spec-comp i x ⟩ 
    exec (comp x HALT) s
    ∎

---------------------------------
-- Graph-based target language --
---------------------------------

-- Constructors for `Codeᵍ` type
pattern PUSHᵍ n c = PUSH' n ! ▸ᵍ c
pattern ADDᵍ c = ADD' ! ▸ᵍ c
pattern POPᵍ c = POP' ! ▸ᵍ c

execᵍ : ∀ {i} → Codeᵍ Instr 0 → Stack → Partial Stack i
execᵍ c = exec (⦅ c ⦆ [])

--------------------------
-- Graph-based compiler --
--------------------------

compᵍ : ∀ {i} → Expr → Codeᵍ Instr i → Codeᵍ Instr i
compᵍ (Val x)    c = PUSHᵍ x c
compᵍ (Add x y)  c = compᵍ x (compᵍ y ( ADDᵍ c ))
compᵍ (Repeat x) c = LABᵍ← (compᵍ x (POPᵍ (JMPᵍ 0F)))


compileᵍ : ∀ {i} → Expr → Codeᵍ Instr i
compileᵍ e = compᵍ e HALTᵍ

mutual
  ≈comp : ∀ {i} {c d : Code Instr ∞} (x : Expr) → c ≈[ i ] d → comp x c ≈[ i ] comp x d
  ≈comp (Val x) b = ≈cong1 b
  ≈comp (Add x y) b = ≈comp x (≈comp y (≈cong1 b))
  ≈comp {i} (Repeat x) b = ≈comp x (≈cong1 (≈REC (∞≈comp {i} _ b)))

  ∞≈comp : ∀ {i} {c d : Code Instr ∞} (x : Expr) → c ≈[ i ] d → ∞comp x c ∞≈[ i ] ∞comp x d
  ≈force (∞≈comp x b) {j} = ≈comp {j} x (≈down b)

-----------------------------------------
-- Calculation of graph-based compiler --
-----------------------------------------

open ≈-Calculation

mutual

  -- specification and calculation of compᵍ

  spec-compᵍ : ∀ {i n} x {e : Vec _ n} {c} → comp x (⦅ c ⦆ e) ≈[ i ] ⦅ compᵍ x c ⦆ e
  spec-compᵍ (Val x) {e} {c} = 
    (PUSH x (⦅ c ⦆ e))
    ≡⟨⟩
    ⦅ PUSHᵍ x c ⦆ e
   ∎
  
  spec-compᵍ (Add x y) {e} {c} = 
    comp x (comp y (ADD (⦅ c ⦆ e)))
    ≡⟨⟩
    comp x (comp y ( ⦅ ADDᵍ c ⦆ e))
    ≈⟨ ≈comp x (spec-compᵍ y) ⟩
    comp x (⦅ compᵍ y ( ADDᵍ c )⦆ e)
    ≈⟨ spec-compᵍ x ⟩
    ⦅ compᵍ x (compᵍ y ( ADDᵍ c ))⦆ e
   ∎
  
  spec-compᵍ {i} (Repeat x) {e} {c} =
    let e' = REC (∞⦅ compᵍ (Repeat x) c ⦆ e) ∷ e
    in
    comp x (POP (REC (∞comp (Repeat x) (⦅ c ⦆ e))))
    ≈⟨ ≈comp x (≈cong1 (≈REC (∞spec-compᵍ {i} (Repeat x) {c = c}))) ⟩
    comp x (POP (⦅ JMPᵍ 0F ⦆ e'))
    ≡⟨⟩
    comp x (⦅ POPᵍ (JMPᵍ 0F) ⦆ e')
    ≈⟨ spec-compᵍ x ⟩
    ⦅ compᵍ x (POPᵍ (JMPᵍ 0F)) ⦆ e'
    ≡⟨⟩
    ⦅ LABᵍ← (compᵍ x (POPᵍ (JMPᵍ 0F))) ⦆ e
   ∎
  
  ∞spec-compᵍ : ∀ {i n} x {e : Vec _ n} {c} → ∞comp x (⦅ c ⦆ e) ∞≈[ i ] ∞⦅ compᵍ x c ⦆ e
  ≈force (∞spec-compᵍ x) = spec-compᵍ x


-- specification and calculation of compileᵍ

spec-compileᵍ : ∀ {n i} x {e : Vec _ n} → compile x ≈[ i ] ⦅ compileᵍ x ⦆ e
spec-compileᵍ x {e} = 
  compile x 
  ≡⟨⟩
  comp x HALT
  ≡⟨⟩
  comp x (⦅ HALTᵍ ⦆ e)
  ≈⟨ spec-compᵍ x ⟩
  ⦅ compᵍ x HALTᵍ ⦆ e
  ∎
