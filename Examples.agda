{-# OPTIONS --sized-types #-}

------------------------------------------------------------------------
-- Examples of compiler output for the language with while loops.
------------------------------------------------------------------------

module Examples where

open import While
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List hiding (head)


-- Constructors for sequential instructions
pattern PUSHₛ n = DO (PUSH' n !)
pattern ADDₛ = DO (ADD' !)
pattern POPₛ = DO (POP' !)
pattern JPZₛ l = DO (JPZ' ! ＠ l)


-- example expression
ex1 : Expr
ex1 = While (Val 6) (Val 7)

-- compile to graph code
ex1g : ∀ {l} → compileᵍ {l} ex1 ≡ 
  LABᵍ←  (λ l → PUSHᵍ 6 (LABᵍ→ (λ l' → JPZᵍ l' (PUSHᵍ 7 (POPᵍ (JMPᵍ l)))) HALTᵍ))
ex1g = refl

-- compile to sequential code
ex1s : seqn (compileᵍ ex1) 
  ≡ PUSHₛ 6 ∷ JPZₛ 5 ∷ PUSHₛ 7 ∷ POPₛ ∷ JMPₛ 0 ∷ HALTₛ ∷ []
ex1s = refl


-- example expression (using infix `⊕` as shorthand for `Add`)
ex2 : Expr
ex2 = While (Val 6) (Val 7 ⊕ Val 2) ⊕ Val 5

-- compile to graph code
ex2g : ∀ {l} → compileᵍ {l} ex2 ≡ 
  LABᵍ←(λ l → PUSHᵍ 6 (LABᵍ→ (λ l' → JPZᵍ l' (PUSHᵍ 7 (PUSHᵍ 2 (ADDᵍ (POPᵍ (JMPᵍ l))))))
        (PUSHᵍ 5 (ADDᵍ HALTᵍ))))
ex2g = refl

-- compile to sequential code
ex2s : seqn (compileᵍ ex2) 
  ≡ PUSHₛ 6 ∷ JPZₛ 7 ∷ PUSHₛ 7 ∷ PUSHₛ 2 ∷ ADDₛ ∷ POPₛ ∷ JMPₛ 0 ∷ PUSHₛ 5 ∷ ADDₛ ∷ HALTₛ ∷ []
ex2s = refl

-- example expression
ex3 : Expr
ex3 = Val 2 ⊕ (While (Val 6) (Val 7 ⊕ Val 2) ⊕ Val 5)


-- compile to graph code
ex3g : ∀ {l} → compileᵍ {l} ex3 
  ≡ PUSHᵍ 2 (LABᵍ← (λ l →  PUSHᵍ 6 (LABᵍ→
           (λ l' → JPZᵍ l' (PUSHᵍ 7 (PUSHᵍ 2 (ADDᵍ (POPᵍ (JMPᵍ l))))))
           (PUSHᵍ 5 (ADDᵍ (ADDᵍ HALTᵍ))))))
ex3g = refl

-- compile to sequential code
ex3s : seqn (compileᵍ ex3)
  ≡ PUSHₛ 2 ∷ PUSHₛ 6 ∷ JPZₛ 8 ∷ PUSHₛ 7 ∷ PUSHₛ 2 ∷ ADDₛ 
     ∷ POPₛ ∷ JMPₛ 1 ∷ PUSHₛ 5 ∷ ADDₛ ∷ ADDₛ ∷ HALTₛ ∷ []
ex3s = refl


-- example expression
ex4 : Expr
ex4 = (Val 2 ⊕ While (Val 6) (Val 7 ⊕ Val 2)) ⊕ Val 5

-- compile to sequential code
ex4s : seqn (compileᵍ ex4)
  ≡ PUSHₛ 2 ∷ PUSHₛ 6 ∷ JPZₛ 8 ∷ PUSHₛ 7 ∷ PUSHₛ 2 ∷ ADDₛ
     ∷ POPₛ ∷ JMPₛ 1 ∷ ADDₛ ∷ PUSHₛ 5 ∷ ADDₛ ∷ HALTₛ ∷ []
ex4s = refl