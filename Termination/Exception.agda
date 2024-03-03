
-- Here we give a separate proof that the virtual machine `exec` for
-- the language with exceptions is terminating.

module Termination.Exception where

open import Exception

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Agda.Builtin.Nat
open import Data.Nat

open import Data.Product 
open import Data.List hiding (lookup)

-- Define the measure that is used to show that exec is well-founded

csize : Code → ℕ
csize (PUSH x c) =  suc (csize c)
csize (ADD c) =  suc (csize c)
csize (MARK c c') = suc (csize c + csize c')
csize HALT = 1
csize THROW = 1
csize (UNMARK c) = suc (csize c)


ssize : Stack → ℕ
ssize [] = 0
ssize (VAL x ∷ s) =  ssize s
ssize (HAN c ∷ s) =  csize c + ssize s


-- We define exec' which is a variant of exec with an explicit fuel
-- argument that ensures termination. We will show that exec' is
-- equivalen to exec. The size measure defined above defines exactly
-- how much fuel we have to provide.

mutual
    exec' : ℕ → Code → Stack → Stack
    exec' 0 _ _ = []
    exec' (suc j) (PUSH n c) s = exec' j c (VAL n ∷ s)
    exec' (suc j) (ADD c) (VAL n ∷ VAL m ∷ s) = exec' j c (VAL (m + n) ∷ s)
    exec' (suc j) (UNMARK c) (VAL v ∷ HAN c' ∷ s) = exec' j c (VAL v ∷ s)
    exec' (suc j) (MARK c' c) s = exec' j c (HAN c' ∷ s)
    exec' (suc j) THROW s = fail' j s
    exec' _ HALT s = s
    exec' _ _ _ = []

    fail' : ℕ → Stack → Stack
    fail' j (VAL _ ∷ s) = fail' j s
    fail' j (HAN c ∷ s) = exec' j c s
    fail' _ _ = []

open ≤-Reasoning

-- Finally we show that exec' is equivalent to exec.

mutual
  execEq : ∀ c s → (j : ℕ) → (csize c + ssize s ≤ j) → exec c s ≡ exec' j c s
  execEq (PUSH x c) s .(suc _) (s≤s le) = execEq c _ _ le
  execEq (ADD c) [] .(suc _) (s≤s le) = refl
  execEq (ADD c) (VAL x ∷ []) .(suc _) (s≤s le) = refl
  execEq (ADD c) (VAL n ∷ VAL m ∷ s) .(suc _) (s≤s le) = execEq c ((VAL (m + n) ∷ s))  _ le
  execEq (ADD c) (VAL x ∷ HAN _ ∷ s) .(suc _) (s≤s le) = refl
  execEq (ADD c) (HAN x ∷ s) .(suc _) (s≤s le) = refl
  execEq (UNMARK c) [] .(suc _) (s≤s le) = refl
  execEq (UNMARK c) (VAL x ∷ []) .(suc _) (s≤s le) = refl
  execEq (UNMARK c) (VAL x ∷ VAL x₁ ∷ s) .(suc _) (s≤s le) = refl
  execEq (UNMARK c) (VAL x ∷ HAN x₁ ∷ s) .(suc _) (s≤s le) = execEq c _ _ (lemma {csize c} le)
    where lemma : ∀ {a} {b} {c} {n} → a + (b + c) ≤ n → a + c ≤ n
          lemma {a} {b} {c} {n} le =
            begin
            a + c
            ≤⟨ +-mono-≤ (≤-refl {a})  (m≤n+m c b)  ⟩
            a + (b + c)
            ≤⟨  le ⟩
            n
            ∎
  execEq (UNMARK c) (HAN x ∷ s) .(suc _) (s≤s le) = refl

  execEq (MARK c c') s .(suc _) (s≤s le) = execEq c' _ _ (lemma {csize c} le) 
    where lemma : ∀ {a} {b} {c} {n} → a + b + c ≤ n → b + (a + c) ≤ n
          lemma {a} {b} {c} {n} le =
            begin
            b + (a + c)
            ≡˘⟨ +-assoc b a c  ⟩
            (b + a) + c
            ≡⟨  cong₂ _+_ (+-comm b a) refl ⟩
            a + b + c
            ≤⟨  le ⟩
            n
            ∎
  execEq THROW s .(suc _) (s≤s le) = failEq s _ le
  execEq HALT s .(suc _) (s≤s le) = refl

  failEq : ∀ s → (j : ℕ) → (ssize s ≤ j) → fail s ≡ fail' j s
  failEq [] j le = refl
  failEq (VAL x ∷ s) j le =  failEq s j le
  failEq (HAN c ∷ s) j le =  execEq c s j le

-- This shows that exec is equivalent to exec'

bisim : ∀ c s →  exec c s ≡ exec' (csize c + ssize s) c s
bisim c s = execEq c s (csize c + ssize s) ≤-refl
