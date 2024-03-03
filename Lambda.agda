{-# OPTIONS --copatterns --sized-types #-}


------------------------------------------------------------------------
-- Calculation for call-by-value lambda calculus with integers and
-- addition.
------------------------------------------------------------------------

module Lambda where


open import Partial
open import Data.Nat
open import Agda.Builtin.Nat
open import Data.Bool 
open import Data.Product
open import Data.List hiding (lookup)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

---------------------
-- Source language --
---------------------

data Expr : Set where
  Val : ℕ → Expr
  Add : Expr → Expr → Expr
  Abs : Expr → Expr
  App : Expr → Expr → Expr
  Var : ℕ → Expr

mutual
  data Value : Set where
    Num : ℕ → Value
    Clo : Expr → Env → Value

  Env : Set
  Env = List Value


lookup : ∀ {a i} → ℕ → List a → Partial a i
lookup 0 (x ∷ xs) = return x
lookup (suc i) (x ∷ xs) = lookup i xs
lookup _ _ = never


-- The following two functions are used instead of partial pattern
-- matching. 

getNum : ∀ {i} → Value → Partial ℕ i
getNum (Num n) = return n
getNum _ = never

getClo : ∀ {i} → Value → Partial (Expr × Env) i
getClo (Clo x e) = return (x , e)
getClo _ = never


mutual
  eval : ∀ {i} → Expr → Env → Partial Value i
  eval (Val x) e = return (Num x)
  eval (Add x y) e =
    do n ← eval x e >>= getNum
       m ← eval y e >>= getNum
       return (Num (n + m))
  eval (Var i) e = lookup i e
  eval (Abs x)   e = return (Clo x e)
  eval (App x y) e = do (x' , e') ← eval x e >>= getClo
                        v ← eval y e
                        later (∞eval x' (v ∷ e'))

  ∞eval : ∀ {i} → Expr → Env → ∞Partial Value i
  force (∞eval x e) = eval x e


--------------------------------
-- Tree-based target language --
--------------------------------

data Code : Set where
  PUSH : ℕ → Code → Code
  ADD : Code → Code
  LOOKUP : ℕ → Code → Code
  RET : Code
  APP : Code → Code
  ABS : Code → Code → Code
  HALT : Code

mutual
  data Value' : Set where
    Num' : ℕ → Value'
    Clo' : Code → Env' → Value'

  Env' : Set
  Env' = List Value'
  

data Elem : Set where
  VAL : Value' → Elem
  CLO : Code → Env' → Elem


Stack : Set
Stack = List Elem

Conf : Set
Conf = Stack × Env'


-- We use the TERMINATING pragma since Agda does not recognize that
-- `exec` is terminating. We prove that `exec` is terminating
-- separately in the `Termination.Lambda` module.

mutual
  {-# TERMINATING #-}
  exec : ∀ {i} → Code → Conf → Partial Conf i
  exec (PUSH n c) (s , e) = exec c (VAL (Num' n) ∷ s , e)
  exec (ADD c) (VAL (Num' n) ∷ VAL (Num' m) ∷ s , e) = exec c (VAL (Num' (m + n)) ∷ s , e)
  exec (LOOKUP n c) (s , e) = do v ← lookup n e
                                 exec c (VAL v ∷ s , e)
  exec RET  (VAL u ∷ CLO c e' ∷ s , _) = exec c (VAL u ∷ s , e')
  exec (APP c) (VAL v ∷ VAL (Clo' c' e') ∷ s , e) = later (∞exec c' (CLO c e ∷ s , v ∷ e'))
  exec (ABS c' c) (s , e) = exec c (VAL (Clo' c' e) ∷ s , e)
  exec HALT c = return c
  exec _ _ = never


  ∞exec : ∀ {i} → Code → Conf → ∞Partial Conf i
  force (∞exec c e) = exec c e



-------------------------
-- Tree-based compiler --
-------------------------

comp : Expr → Code → Code
comp (Val n) c =  PUSH n c
comp (Add x y) c = comp x (comp y (ADD c))
comp (Var i) c = LOOKUP i c
comp (App x y) c = comp x (comp y (APP c))
comp (Abs x) c = ABS (comp x RET) c

compile : Expr → Code
compile e = comp e HALT



----------------------------------------
-- Calculation of tree-based compiler --
----------------------------------------

-- The conversion function that is used to state the correctness
-- property for comp.

mutual
  conv : Value → Value'
  conv (Clo x' e') = Clo' (comp x' RET) (convE e')
  conv (Num n) = Num' n

  convE : Env → Env'
  convE [] = []
  convE (x ∷ xs) = conv x ∷ convE xs


-- This is the lookup lemma that is used in the `Var` case of the
-- calculation.

lookup-conv : ∀ {i A} n e → (f : Value' → Partial A ∞) →
  (lookup n e >>= (f ∘ conv)) ~[ i ] (lookup n (convE e) >>= f)
lookup-conv zero (x ∷ e) f =  ~irefl
lookup-conv (suc n) (x ∷ e) f = lookup-conv n e f
lookup-conv (suc n) [] f =  ~itrans ~inever->>=  ( ~isymm ~inever->>= )
lookup-conv zero [] f = ~itrans ~inever->>=  ( ~isymm ~inever->>= )


module TreeComp where
  open ~i-Calculation

  -- specification and calculation of comp

  spec-comp : ∀ i x {s c e} →
    (do v ← eval x e
        exec c (VAL (conv v) ∷ s , convE e))
    ~[ i ]
    (exec (comp x c) (s , convE e))
  spec-comp zero _ =  ~izero
  spec-comp i (Val x) {s} {c} {e}  =
    (do v ← eval (Val x) e
        exec c (VAL (conv v) ∷ s , convE e))
    ≡⟨⟩
    (exec (comp (Val x) c) (s , convE e))
    ∎
  spec-comp i (Add x y) {s} {c} {e} =
    (do v ← eval (Add x y) e
        exec c (VAL (conv v) ∷ s , convE e))
    ≡⟨⟩
    (do v ← (do n ← eval x e >>= getNum
                m ← eval y e >>= getNum
                return (Num (n + m)))
        exec c (VAL (conv v) ∷ s , convE e))
    ~⟨ ~i>>=-assoc (eval x e >>= getNum) ⟩
    (do n ← eval x e >>= getNum
        v ← (do m ← eval y e >>= getNum
                return (Num (n + m)))
        exec c (VAL (conv v) ∷ s , convE e))
    ~⟨ ~i>>=-cong-r (eval x e >>= getNum) (\ n -> ~i>>=-assoc (eval y e >>= getNum))⟩
    (do n ← eval x e >>= getNum
        m ← eval y e >>= getNum
        exec c (VAL (Num' (n + m)) ∷ s , convE e))
    ≡⟨⟩
    (do n ← eval x e >>= getNum
        m ← eval y e >>= getNum
        exec (ADD c) (VAL (Num' m) ∷ VAL (Num' n) ∷ s , convE e))
    ~⟨ ~i>>=-assoc (eval x e) ⟩
    (do n' ← eval x e
        n ← getNum n'
        m ← eval y e >>= getNum
        exec (ADD c) (VAL (Num' m) ∷ VAL (Num' n) ∷ s , convE e))
    ~⟨  ~i>>=-cong-r (eval x e) (λ {(Num n) → ~irefl;
        (Clo _ _) → ~itrans ~inever->>= ( ~isymm ( ~i>>=-never (eval y e >>= getNum)))}) 
    ⟩
    (do n ← eval x e
        m ← eval y e >>= getNum
        exec (ADD c) (VAL (Num' m) ∷ VAL (conv n) ∷ s , convE e))
    ~⟨  ~i>>=-cong-r (eval x e) ( λ n →
          ~itrans (~i>>=-assoc (eval y e)) (~i>>=-cong-r (eval y e) 
          (λ {(Num n) → ~irefl;
          (Clo _ _) → ~inever->>=})))⟩
    (do n ← eval x e
        m ← eval y e
        exec (ADD c) (VAL (conv m) ∷ VAL (conv n) ∷ s , convE e))
    ~⟨  ~i>>=-cong-r (eval x e) (λ n → spec-comp i y ) ⟩
    (do n ← eval x e
        exec (comp y (ADD c)) (VAL (conv n) ∷ s , convE e))
    ~⟨ spec-comp i x ⟩
    (exec (comp x (comp y (ADD c))) (s , convE e))
    ∎  

  spec-comp i (Var n) {s} {c} {e} =
    (do v ← eval (Var n) e
        exec c (VAL (conv v) ∷ s , convE e))
    ≡⟨⟩
    (do v ← lookup n e
        exec c (VAL (conv v) ∷ s , convE e))
    ~⟨ lookup-conv n e _ ⟩
    (do v ← lookup n (convE e)
        exec c (VAL v ∷ s , convE e))
    ≡⟨⟩
    (exec (LOOKUP n c) (s , convE e))
    ∎

  spec-comp i@(suc j) (App x y) {s} {c} {e} =
    (do v ← eval (App x y) e
        exec c (VAL (conv v) ∷ s , convE e))
    ≡⟨⟩
    (do v ← do x' , e' ← eval x e >>= getClo
               v ← eval y e
               later (∞eval x' (v ∷ e'))
        exec c (VAL (conv v) ∷ s , convE e))
    ~⟨ ~i>>=-assoc ( eval x e >>= getClo) ⟩
    (do x' , e' ← eval x e >>= getClo
        v ← do v ← eval y e
               later (∞eval x' (v ∷ e'))
        exec c (VAL (conv v) ∷ s , convE e))
    ~⟨ ~i>>=-cong-r (eval x e >>= getClo) (λ _ → ~i>>=-assoc (eval y e)) ⟩
    (do x' , e' ← eval x e >>= getClo
        v ← eval y e
        w ← later (∞eval x' (v ∷ e'))
        exec c (VAL (conv w) ∷ s , convE e))
    ≡⟨⟩
    (do x' , e' ← eval x e >>= getClo
        v ← eval y e
        w ← later (∞eval x' (v ∷ e'))
        exec RET (VAL (conv w) ∷ CLO c (convE e) ∷ s , convE (v ∷ e')))
    ≡⟨⟩
    (do x' , e' ← eval x e >>= getClo
        v ← eval y e
        later(∞eval x' (v ∷ e') ∞>>= λ w →
          exec RET (VAL (conv w) ∷ CLO c (convE e) ∷ s , convE (v ∷ e'))))
    ~⟨ ~i>>=-cong-r (eval x e >>= getClo) (λ (x' , e') → ~i>>=-cong-r (eval y e)
                  (λ v →  ~ilater ( spec-comp j x') )) ⟩
    (do x' , e' ← eval x e >>= getClo
        v ← eval y e
        later (∞exec (comp x' RET) (CLO c (convE e) ∷ s , convE (v ∷ e'))))
    ≡⟨⟩
    (do x' , e' ← eval x e >>= getClo
        v ← eval y e
        exec (APP c) (VAL (conv v) ∷ VAL (Clo' (comp x' RET) (convE e')) ∷ s , convE e))
    ~⟨ ~itrans (~i>>=-assoc (eval x e)) ( ~i>>=-cong-r (eval x e)
        λ {(Num _) →  ~itrans ~inever->>= (~isymm (~i>>=-never (eval y e))) ;
          (Clo x e) → ~irefl}) ⟩
    (do w ← eval x e
        v ← eval y e
        exec (APP c) (VAL (conv v) ∷ VAL (conv w) ∷ s , convE e))
    ~⟨ ~i>>=-cong-r (eval x e) (λ w → spec-comp i y) ⟩
    (do w ← eval x e
        exec (comp y (APP c)) (VAL (conv w) ∷ s , convE e))
    ~⟨ spec-comp i x ⟩
    (exec (comp x (comp y (APP c))) (s , convE e))
    ∎

  spec-comp i (Abs x) {s} {c} {e} =
    (do v ← eval (Abs x) e
        exec c (VAL (conv v) ∷ s , convE e))
    ≡⟨⟩ -- definition of eval & conv
    (exec c (VAL (Clo' (comp x RET) (convE e)) ∷ s , convE e))
    ≡⟨⟩ -- definition of exec (ABS c) 
    (exec (ABS (comp x RET) c) (s , convE e))
    ∎



  -- specification and calculation of compile

  spec-compile : ∀ i x {s e} →
    (do n ← eval x e ; return (VAL (conv n) ∷ s , convE e)) ~[ i ] exec (compile x) (s , convE e)
  spec-compile i x {s} {e} =
    (do n ← eval x e ; return (VAL (conv n) ∷ s , convE e)) 
    ≡⟨⟩
    (do n ← eval x e ; exec HALT (VAL (conv n) ∷ s , convE e)) 
    ~⟨ spec-comp i x ⟩ 
    exec (comp x HALT) (s , convE e)
    ∎

---------------------------------
-- Graph-based target language --
---------------------------------

data Codeᵍ (l : Set) : Set where
  PUSHᵍ : ℕ → Codeᵍ l → Codeᵍ l
  ADDᵍ : Codeᵍ l → Codeᵍ l
  LOOKUPᵍ : ℕ → Codeᵍ l → Codeᵍ l
  RETᵍ : Codeᵍ l
  APPᵍ : Codeᵍ l → Codeᵍ l
  ABSᵍ : l → Codeᵍ l → Codeᵍ l
  HALTᵍ : Codeᵍ l
  JMPᵍ : l → Codeᵍ l
  LABᵍ→ : (l → Codeᵍ l) → Codeᵍ l → Codeᵍ l

⦅_⦆ : Codeᵍ Code → Code
⦅ PUSHᵍ n c ⦆ = PUSH n ⦅ c ⦆
⦅ ADDᵍ c ⦆ = ADD ⦅ c ⦆
⦅ LOOKUPᵍ n c ⦆ = LOOKUP n ⦅ c ⦆
⦅ RETᵍ ⦆ = RET
⦅ ABSᵍ l c ⦆ = ABS l ⦅ c ⦆
⦅ APPᵍ c ⦆ = APP ⦅ c ⦆
⦅ HALTᵍ ⦆ = HALT
⦅ JMPᵍ l ⦆ = l
⦅ LABᵍ→ f c ⦆ = ⦅ f ⦅ c ⦆ ⦆

execᵍ : (∀ {l} → Codeᵍ l) → Conf → Partial Conf ∞
execᵍ c = exec ⦅ c ⦆

--------------------------
-- Graph-based compiler --
--------------------------

compᵍ : ∀ {l} → Expr → Codeᵍ l → Codeᵍ l
compᵍ (Val n) c =  PUSHᵍ n c
compᵍ (Add x y) c = compᵍ x (compᵍ y (ADDᵍ c))
compᵍ (Var i) c = LOOKUPᵍ i c
compᵍ (App x y) c = compᵍ x (compᵍ y (APPᵍ c))
compᵍ (Abs x) c = LABᵍ→ (λ l → ABSᵍ l c) (compᵍ x RETᵍ)

compileᵍ : Expr → (∀ {l} → Codeᵍ l)
compileᵍ e = compᵍ e HALTᵍ


-----------------------------------------
-- Calculation of graph-based compiler --
-----------------------------------------

-- spec-compification and calculation of compᵍ

open ≡-Reasoning

-- specification and calculation of compᵍ

spec-compᵍ : ∀ x {c} → comp x ⦅ c ⦆ ≡ ⦅ compᵍ x c ⦆
spec-compᵍ (Val x) {c} = 
  begin
  PUSH x ⦅ c ⦆
  ≡⟨⟩
  ⦅ PUSHᵍ x c ⦆
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

spec-compᵍ (Var n) {c} =
  begin
  LOOKUP n ⦅ c ⦆
  ≡⟨⟩
  ⦅ LOOKUPᵍ n c ⦆
  ∎

spec-compᵍ (Abs x) {c} =
  begin
  ABS (comp x RET) ⦅ c ⦆
  ≡⟨⟩
  ABS (comp x ⦅ RETᵍ ⦆) ⦅ c ⦆
  ≡⟨ cong₂ ABS (spec-compᵍ x) refl ⟩
  ABS ⦅ compᵍ x RETᵍ ⦆ ⦅ c ⦆
  ≡⟨⟩
  (λ l → ABS l ⦅ c ⦆) ⦅ compᵍ x RETᵍ ⦆
  ≡⟨⟩
  (λ l → ⦅ ABSᵍ l c ⦆) ⦅ compᵍ x RETᵍ ⦆
  ≡⟨⟩
  ⦅ LABᵍ→ (λ l → ABSᵍ l c) (compᵍ x RETᵍ) ⦆
  ∎

spec-compᵍ (App x y) {c} = 
  begin
  comp x (comp y (APP ⦅ c ⦆))
  ≡⟨⟩
  comp x (comp y ( ⦅ APPᵍ c ⦆))
  ≡⟨ cong (comp x) (spec-compᵍ y) ⟩
  comp x ⦅ compᵍ y ( APPᵍ c )⦆
  ≡⟨ spec-compᵍ x ⟩
  ⦅ compᵍ x (compᵍ y ( APPᵍ c ))⦆
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