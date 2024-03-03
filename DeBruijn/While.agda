{-# OPTIONS --sized-types #-}

------------------------------------------------------------------------
-- Calculation for a simple arithmetic expression language extended
-- with While loops.
------------------------------------------------------------------------

module DeBruijn.While where

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
  While : Expr → Expr → Expr

mutual
  eval : ∀ {i} → Expr → Partial ℕ i
  eval (Val x) = return x
  eval (Add x y) =
    do n ← eval x
       m ← eval y
       return (n + m)
  eval (While x y) = do n ← eval x
                        if n ≡ᵇ 0 then return 0
                                  else eval y >> later (∞eval (While x y))

  ∞eval : ∀ {i} → Expr → ∞Partial ℕ i
  force (∞eval x) = eval x


--------------------------------
-- Tree-based target language --
--------------------------------


data Instr : ℕ → Set where
 PUSH' : ℕ → Instr 0
 ADD' : Instr 0
 POP' : Instr 0
 JPZ' : Instr 1


-- Constructors for `Code` type
pattern PUSH n c = PUSH' n ! ▸ c
pattern ADD c = ADD' ! ▸ c
pattern POP c = POP' ! ▸ c
pattern JPZ l c = JPZ' ! ＠ l ▸ c

Stack : Set
Stack = List ℕ


mutual
  exec : ∀ {i} → Code Instr ∞ → Stack → Partial Stack i
  exec (PUSH n c)  s          = exec c (n ∷ s)
  exec (ADD c)    (m ∷ n ∷ s) = exec c ((n + m) ∷ s)
  exec (POP c)    (_ ∷ s)     = exec c s
  exec (JPZ c' c) (n ∷ s)     = if n ≡ᵇ 0 then exec c' (0 ∷ s) else exec c s
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
  comp (Val n)     c = PUSH n c
  comp (Add x y)   c = comp x (comp y (ADD c))
  comp (While x y) c = comp x (JPZ c (comp y (POP (REC (∞comp (While x y) c)))))

  ∞comp : ∀ {i} → Expr → Code Instr i → ∞Code Instr i
  cforce (∞comp x c) = comp x c



compile : ∀ {i} → Expr → Code Instr i
compile e = comp e HALT


----------------------------------------
-- Calculation of tree-based compiler --
----------------------------------------

-- lemma for the calculation

ifzero-cong : ∀ {i A} {p1 p2 q1 q2 : Partial A ∞} n
  → p1 ~[ i ] q1 → p2 ~[ i ] q2
  → (if n ≡ᵇ 0 then p1 else p2) ~[ i ] (if n ≡ᵇ 0 then q1 else q2)
ifzero-cong zero b1 b2 = b1
ifzero-cong (suc n) b1 b2 = b2

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
    
  spec-comp i@(suc j) (While x y) {s} {c} =
    (do v ← eval (While x y) ; exec c (v ∷ s))
    ≡⟨⟩
    (do v ← do n ← eval x ; if n ≡ᵇ 0 then return 0 else eval y >> later (∞eval (While x y))
        exec c (v ∷ s))
    ~⟨ (~i>>=-assoc' (eval x) λ { zero → ~irefl ; (suc n) → ~i>>=-assoc (eval y)})⟩ 
    (do n ← eval x
        if n ≡ᵇ 0 then exec c (0 ∷ s) else do eval y ; later (∞eval (While x y) ∞>>= λ m → exec c (m ∷ s)))
    ~⟨ (~i>>=-cong-r (eval x) λ n → ifzero-cong n ~irefl (~i>>=-cong-r (eval y) λ _ → ~ilater (spec-comp j (While x y) {s} {c}))) ⟩
    (do n ← eval x
        if n ≡ᵇ 0 then exec c (0 ∷ s) else do eval y ; later (∞exec (comp (While x y) c) s))
    ~⟨ (((~i>>=-cong-r (eval x) λ { zero → ~irefl ; (suc n) → ~i>>=-cong-r (eval y) λ _ → ~ilater ~irefl}))) ⟩
    (do n ← eval x
        if n ≡ᵇ 0 then exec c (0 ∷ s) else do eval y ; exec (REC (∞comp (While x y) c)) s)
    ≡⟨⟩
    (do n ← eval x
        if n ≡ᵇ 0 then exec c (0 ∷ s) else do m ← eval y ; exec (POP (REC (∞comp (While x y) c))) (m ∷ s))
    ~⟨ ((~i>>=-cong-r (eval x) λ { zero → ~irefl ; (suc n) → spec-comp i y })) ⟩
    (do n ← eval x
        if n ≡ᵇ 0 then exec c (0 ∷ s) else do exec (comp y (POP (REC (∞comp (While x y) c)))) s)
    ~⟨ (((~i>>=-cong-r (eval x) λ { zero → ~irefl ; (suc n) → ~irefl }))) ⟩
    (do n ← eval x
        exec (JPZ c (comp y (POP (REC (∞comp (While x y) c))))) (n ∷ s))
    ~⟨ spec-comp i x ⟩
    (exec (comp x (JPZ c (comp y (POP (REC (∞comp (While x y) c)))))) s)
    ∎


  -- specification and calculation of compile

  spec-compile : ∀ i x {s} →
    (do v ← eval x; return (v ∷ s)) ~[ i ] exec (compile x) s
  spec-compile i x {s} = 
    (do v ← eval x; return (v ∷ s)) 
    ≡⟨⟩
    (do v ← eval x; exec HALT (v ∷ s)) 
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
pattern JPZᵍ l c = JPZ' ! ＠ l ▸ᵍ c

execᵍ : ∀ {i} → Codeᵍ Instr 0 → Stack → Partial Stack i
execᵍ c = exec (⦅ c ⦆ [])


--------------------------
-- Graph-based compiler --
--------------------------

compᵍ : ∀ {i} → Expr → Codeᵍ Instr i → Codeᵍ Instr i
compᵍ (Val x)     c = PUSHᵍ x c
compᵍ (Add x y)   c = compᵍ x (compᵍ y ( ADDᵍ c ))
compᵍ (While x y) c = LABᵍ← (LABᵍ→ (compᵍ x (JPZᵍ 0F (compᵍ y (POPᵍ (JMPᵍ 1F))))) (⇑ c))


compileᵍ : ∀ {i} → Expr → Codeᵍ Instr i
compileᵍ e = compᵍ e HALTᵍ


-- ≈ is a congruence for `comp`
mutual
  ≈comp : ∀ {i} {c d : Code Instr ∞} (x : Expr) → c ≈[ i ] d → comp x c ≈[ i ] comp x d
  ≈comp (Val x) b = ≈cong1 b
  ≈comp (Add x y) b = ≈comp x (≈comp y (≈cong1 b))
  ≈comp {i} (While x y) b = ≈comp x (≈cong2 b (≈comp y (≈cong1 (≈REC (∞≈comp {i} _ b)))))

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
  
  spec-compᵍ {i} (While x y) {e} {c} =
    let e' = REC (∞⦅ compᵍ (While x y) c ⦆ e) ∷ e
        e'' = ⦅ ⇑ c ⦆ e' ∷ e'
    in
    comp x (JPZ (⦅ c ⦆ e) (comp y (POP (REC (∞comp (While x y) (⦅ c ⦆ e))))))
    ≈⟨ ≈comp x ((≈cong1 (≈comp y (≈cong1 (≈REC (∞spec-compᵍ {i} (While x y))))))) ⟩
    comp x (JPZ (⦅ c ⦆ e) (comp y (POP (⦅ JMPᵍ 1F ⦆ e''))))
    ≡⟨⟩
    comp x (JPZ (⦅ c ⦆ e) (comp y (⦅ POPᵍ (JMPᵍ 1F) ⦆ e'')))
    ≈⟨ ≈comp x (≈cong1 (spec-compᵍ y)) ⟩
    comp x (JPZ (⦅ c ⦆ e)  (⦅ compᵍ y (POPᵍ (JMPᵍ 1F)) ⦆ e''))
    ≈⟨  ≈comp x (≈cong2 (unravel⇑ c e _) ≈refl) ⟩
    comp x (JPZ (⦅ ⇑ c ⦆ e')  (⦅ compᵍ y (POPᵍ (JMPᵍ 1F)) ⦆ e''))
    ≡⟨⟩
    comp x (⦅ JPZᵍ 0F (compᵍ y (POPᵍ (JMPᵍ 1F))) ⦆ e'')
    ≈⟨ spec-compᵍ x ⟩
    ⦅ compᵍ x (JPZᵍ 0F (compᵍ y (POPᵍ (JMPᵍ 1F)))) ⦆ e''
    ≡⟨⟩
    ⦅ LABᵍ→ (compᵍ x (JPZᵍ 0F (compᵍ y (POPᵍ (JMPᵍ 1F))))) (⇑ c) ⦆ e'
    ≡⟨⟩
    ⦅ LABᵍ← (LABᵍ→ (compᵍ x (JPZᵍ 0F (compᵍ y (POPᵍ (JMPᵍ 1F))))) (⇑ c)) ⦆ e
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