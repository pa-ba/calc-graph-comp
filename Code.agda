{-# OPTIONS --sized-types #-}

------------------------------------------------------------------------
-- This module defines a generic tree-shaped code type `Code` and a
-- correspoinding graph-shaped code type `Codeᵍ`. Both types are
-- indexed by a finite container type that defines the instructions
-- that are available.
------------------------------------------------------------------------

module Code where

open import Size public
open import Data.Nat
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])

-- We want to parametrise the tree and the graph type with a type `I :
-- Set → Set` of finite containers. We represent such finte
-- containiers as `I : ℕ → Set`. Such an `I` then gives rise to the
-- finite container `λ A → Cont I A 0`.

data Cont (I : ℕ → Set) (A : Set) : ℕ → Set where
  _! : ∀ {n} → I n → Cont I A n
  _＠_ : ∀ {n} → Cont I A (suc n) → A → Cont I A n
infixl 5 _＠_

-- finite containers are functors
mapC : ∀ {I n A B} → (A → B) → Cont I A n → Cont I B n
mapC f (x !) = x !
mapC f (c ＠ x) = mapC f c ＠ f x

--------------------------
-- Tree-structured code --
--------------------------

mutual
  data Code (I : ℕ → Set) (i : Size) : Set where
    _▸_ : Cont I (Code I i) 0 → Code I i → Code I i
    HALT : Code I i
    REC : ∞Code I i → Code I i
  
  record ∞Code (I : ℕ → Set)  (i : Size) : Set where
    coinductive
    constructor rec
    field
      cforce :  {j : Size< i} → Code I j

open ∞Code public

infixl 4 _▸_

--------------------------------------------------
-- Size-indexed bisimilarity relation on `Code` --
--------------------------------------------------

infix 3 _≈[_]_
infix 3 _∞≈[_]_

mutual
  
  data _≈[_]_ {I : ℕ → Set} : Code I ∞ → Size → Code I ∞ → Set where
    ≈HALT : ∀ {i} → HALT ≈[ i ] HALT
    ≈REC : ∀ {i c d} → c ∞≈[ i ] d → REC c ≈[ i ] REC d
    ≈▸ : ∀ {i a b c d} → a c≈[ i ] b → c ≈[ i ] d → a ▸ c ≈[ i ] b ▸ d
  
  record _∞≈[_]_ {I : ℕ → Set} (c : ∞Code I ∞) (i : Size) (d : ∞Code I ∞) : Set where
    coinductive
    constructor ≈mk
    field
      ≈force :  {j : Size< i} → cforce c ≈[ j ] cforce d

  data _c≈[_]_  {n} {I : ℕ → Set} : Cont I (Code I ∞) n → Size → Cont I (Code I ∞) n → Set where
    ≈! : ∀ {i c} → (c !) c≈[ i ] (c !)
    ≈＠ : ∀ {i c d a b} → c c≈[ i ] d → a ≈[ i ] b → (c ＠ a) c≈[ i ] (d ＠ b)

open _∞≈[_]_ public

-- reflexivity of bisimilarity

mutual
  ≈refl : ∀ {I i} {c : Code I ∞} → c ≈[ i ] c
  ≈refl {c = x ▸ c} = ≈▸ c≈refl ≈refl 
  ≈refl {c = HALT} = ≈HALT
  ≈refl {c = REC x} = ≈REC ∞≈refl

  c≈refl : ∀ {I i n} {c : Cont I (Code I ∞) n} → c c≈[ i ] c
  c≈refl {c = x !} = ≈!
  c≈refl {c = c ＠ x} = ≈＠ c≈refl ≈refl

  ∞≈refl : ∀ {I i} {c : ∞Code I ∞} → c ∞≈[ i ] c
  ≈force ∞≈refl = ≈refl

-- Congruence of bisimilarity w.r.t. finite containers

≈cong1 : ∀ {I : ℕ → Set} {i a} {c d : Code I ∞} → c ≈[ i ] d → a ▸ c ≈[ i ] a ▸ d
≈cong1 b = ≈▸ c≈refl b

≈cong2 : ∀ {I : ℕ → Set} {i a} {c c' d d' : Code I ∞} → c' ≈[ i ] d' → c ≈[ i ] d → (a ＠ c') ▸ c ≈[ i ] (a ＠ d') ▸ d
≈cong2 b1 b2 = ≈▸ (≈＠ c≈refl b1) b2


-- Transitivity of bisimilarity
mutual
  ≈trans : ∀ {I i} {c1 c2 c3 : Code I ∞} → c1 ≈[ i ] c2 → c2 ≈[ i ] c3 → c1 ≈[ i ] c3
  ≈trans ≈HALT ≈HALT = ≈HALT
  ≈trans (≈REC b1) (≈REC b2) = ≈REC (∞≈trans  b1 b2 )
  ≈trans (≈▸ b1 b1') (≈▸ b2 b2') = ≈▸ (c≈trans b1 b2) (≈trans b1' b2')
  
  c≈trans : ∀ {I i n} {c1 c2 c3 : Cont I (Code I ∞) n} → c1 c≈[ i ] c2 → c2 c≈[ i ] c3 → c1 c≈[ i ] c3
  c≈trans ≈! ≈! = ≈!
  c≈trans (≈＠ b1 b1') (≈＠ b2 b2') = ≈＠ (c≈trans b1 b2) (≈trans b1' b2')
  
  ∞≈trans : ∀ {I i} {c1 c2 c3 : ∞Code I ∞} → c1 ∞≈[ i ] c2 → c2 ∞≈[ i ] c3 → c1 ∞≈[ i ] c3
  ≈force (∞≈trans b1 b2) = ≈trans (≈force b1) (≈force b2)

-- bisimilarity is downards closed w.r.t. its size index.
mutual
  ≈down : ∀{i I} {c d : Code I ∞} {j : Size< (↑ i)} → c ≈[ i ] d → c ≈[ j ] d
  ≈down ≈HALT = ≈HALT
  ≈down (≈REC x) = ≈REC x
  ≈down (≈▸ x bi) = ≈▸ (c≈down x) (≈down bi)

  c≈down : ∀{i I n} {c d : Cont I (Code I ∞) n} {j : Size< (↑ i)} → c c≈[ i ] d → c c≈[ j ] d
  c≈down ≈! = ≈!
  c≈down (≈＠ bi x) = ≈＠ (c≈down bi) (≈down x)

-- Define notation for calculations
module ≈-Calculation where
  infix  3 _∎
  infixr 1 _≈⟨_⟩_
  infixr 1 _≡⟨⟩_

  _≈⟨_⟩_ : ∀ {I i} (x : Code I ∞) →
    ∀ {y : Code I ∞} {z : Code I ∞} → x ≈[ i ] y → y ≈[ i ] z → x ≈[ i ] z
  _≈⟨_⟩_ {_} x r eq =  ≈trans r eq

  _≡⟨⟩_ : ∀ {I i} (x : Code I ∞) → ∀ {y : Code I ∞} → x ≈[ i ] y → x ≈[ i ] y
  _≡⟨⟩_  x eq = eq

  _∎ : ∀ {I i} (x : Code I ∞) → x ≈[ i ] x
  _∎  x = ≈refl

---------------------------
-- Graph-structured code --
---------------------------

data Codeᵍ (I : ℕ → Set) (l : Set) : Set where
  _▸ᵍ_ : Cont I l 0 → Codeᵍ I l  → Codeᵍ I l
  HALTᵍ : Codeᵍ I l
  LABᵍ→ : (l → Codeᵍ I l) → Codeᵍ I l → Codeᵍ I l
  LABᵍ← : (l → Codeᵍ I l) → Codeᵍ I l
  JMPᵍ : l → Codeᵍ I l

infixl 4 _▸ᵍ_


-- Unravelling transformation

unravI : ∀ {I n} → Cont I (Code I ∞) n → Cont I (Code I ∞) n
unravI (ins !) = ins !
unravI (ins ＠ arg) = unravI ins ＠ arg

mutual
  {-# TERMINATING #-}
  ⦅_⦆ : ∀ {I} → (Codeᵍ I (Code I ∞)) → Code I ∞
  ⦅ ins ▸ᵍ c ⦆ = unravI ins ▸ ⦅ c ⦆
  ⦅ HALTᵍ ⦆ = HALT
  ⦅ LABᵍ→ f c ⦆ = ⦅ f ⦅ c ⦆ ⦆
  ⦅ LABᵍ← f ⦆ = ⦅ f (REC ∞⦅ LABᵍ← f ⦆) ⦆ 
  ⦅ JMPᵍ c ⦆ = c


  ∞⦅_⦆ : ∀ {I} → Codeᵍ I (Code I ∞) → ∞Code I ∞
  cforce ( ∞⦅ c ⦆ ) =  ⦅ c ⦆

-- To prove that unravelling is total we first define a truncated
-- version of unravelling below:
mutual
  ⦅_,_⦆ : ∀ {I} → (Codeᵍ I (Code I ∞)) → ℕ → Code I ∞
  ⦅ ins ▸ᵍ c , n ⦆ = unravI ins ▸ ⦅ c , n ⦆
  ⦅ HALTᵍ  , _ ⦆ = HALT
  ⦅ LABᵍ→ f c , n ⦆ = ⦅ f ⦅ c , n ⦆ , n ⦆
  ⦅ LABᵍ← f , suc n ⦆ = ⦅ f (REC ∞⦅ LABᵍ← f , n ⦆) , n  ⦆ 
  ⦅ LABᵍ← f , 0 ⦆ = HALT
  ⦅ JMPᵍ c , n ⦆ = c

  ∞⦅_,_⦆ : ∀ {I} → (Codeᵍ I (Code I ∞)) → ℕ → ∞Code I ∞
  cforce ( ∞⦅ c , n ⦆ ) = ⦅ c , n ⦆

-- One can show that:
--
--    ⦅c, n⦆ ≋[n] ⦅c⦆   for all n : ℕ,  c : ∀ {l} → Codeᵍ l
--
-- where _≋[_]_ is a step-indexed version of bisimilarity. Hence, ⦅_⦆
-- is productive. However, we cannot prove this within Agda as this
-- requires parametricity. In particular, we need that 
--
--     c ≈[n] c'  implies  ⦅f c⦆ ≈[n] ⦅f c'⦆ 
--
-- for any parametric f : ∀ {l} → l → Codeᵍ I l.

mutual
  mapᵍ : ∀ {I l l'} → (l → l') → (l' → l) → Codeᵍ I l → Codeᵍ I l'
  mapᵍ f g (ins ▸ᵍ c) = mapC f ins ▸ᵍ (mapᵍ f g c)
  mapᵍ f g HALTᵍ = HALTᵍ
  mapᵍ f g (JMPᵍ x) = JMPᵍ (f x)
  mapᵍ f g (LABᵍ→ x c) = LABᵍ→ (λ l' → mapᵍ f g (x (g l'))) (mapᵍ f g c)
  mapᵍ f g (LABᵍ← x) = LABᵍ← (λ l' → mapᵍ f g (x (g l')))


----------------------------------------- 
-- Linearise graphs to sequential code --
----------------------------------------- 


data SeqnElem (I : ℕ → Set) : Set where
  DO : Cont I ℕ 0 → SeqnElem I
  JMPₛ : ℕ → SeqnElem I
  HALTₛ : SeqnElem I

Seqn : (I : ℕ → Set) → Set
Seqn I = List (SeqnElem I)

lengthᵍ : ∀ {I} → Codeᵍ I ℕ → ℕ → ℕ
lengthᵍ (x ▸ᵍ c) a = lengthᵍ c (suc a)
lengthᵍ HALTᵍ a = suc a
lengthᵍ (LABᵍ→ f c) a = lengthᵍ c (lengthᵍ (f 0) a)
lengthᵍ (LABᵍ← f) a = lengthᵍ (f 0) a
lengthᵍ (JMPᵍ x) a = suc a


seqn' : ∀ {I} → Codeᵍ I ℕ → ℕ → Seqn I
seqn' (x ▸ᵍ c) l = DO x ∷ seqn' c (suc l)
seqn' HALTᵍ l = [ HALTₛ ]
seqn' (LABᵍ→ f c) l =
  let l' = lengthᵍ (f 0) l
  in seqn' (f l') l ++ seqn' c l'
seqn' (LABᵍ← f) l = seqn' (f l) l
seqn' (JMPᵍ x) l = [ JMPₛ x ]


seqn : ∀ {I} → (∀ {l} → Codeᵍ I l) → Seqn I
seqn c = seqn' c 0 