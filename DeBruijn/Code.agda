{-# OPTIONS --sized-types #-}

------------------------------------------------------------------------
-- This module defines a generic tree-shaped code type `Code` and a
-- correspoinding graph-shaped code type `Codeᵍ`. Both types are
-- indexed by a finite container type that defines the instructions
-- that are available. However, Codeᵍ uses a de Bruijn representation
-- instead of PHOAS. This allows us to define unravelling in a way
-- that Agda recognises as total, but at the expense of complicating
-- the calculations.
------------------------------------------------------------------------

module DeBruijn.Code where

open import Size public
open import Data.Nat
open import Data.Fin
open import Data.Bool
open import Data.Vec hiding ([_] ; _++_)
open import Data.List hiding (lookup)
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

-- Instead of parametricity we use de Bruijn indices: `Codeᵍ I n`
-- classifies graph-structured code with `n` free labels.

data Codeᵍ (I : ℕ → Set) (n : ℕ) : Set where
  _▸ᵍ_ : Cont I (Fin n) 0 → Codeᵍ I n  → Codeᵍ I n
  HALTᵍ : Codeᵍ I n
  LABᵍ→ : Codeᵍ I (suc n) → Codeᵍ I n → Codeᵍ I n
  LABᵍ← : Codeᵍ I (suc n) → Codeᵍ I n
  JMPᵍ : Fin n → Codeᵍ I n

infixl 4 _▸ᵍ_


-- Unravelling transformation
mutual
  ⦅_⦆ : ∀ {I n i} → Codeᵍ I n → Vec (Code I i) n  → Code I i
  ⦅ ins ▸ᵍ c ⦆ e = unravI ins e ▸ ⦅ c ⦆ e
  ⦅ HALTᵍ ⦆ _ = HALT
  ⦅ LABᵍ→ f c ⦆ e = ⦅ f  ⦆ ( ⦅ c ⦆ e ∷ e)
  ⦅ LABᵍ← f ⦆ e = ⦅ f ⦆ ( REC ( ∞⦅ LABᵍ← f ⦆ e) ∷ e)
  ⦅ JMPᵍ i ⦆ e = lookup e i

  ∞⦅_⦆ : ∀ {I n i} → (Codeᵍ I n) →  Vec (Code I i) n  → ∞Code I i
  cforce ( ∞⦅ f ⦆ e ) =  ⦅ f ⦆ e

  unravI : ∀ {I i n m} → Cont I (Fin m) n → Vec (Code I i) m  → Cont I (Code I i) n
  unravI (ins !) e = ins !
  unravI (ins ＠ arg) e = unravI ins e ＠ lookup e arg


----------------------------------
-- Lemmas for de Bruijn indices --
----------------------------------

_<b_ : ∀ {n m} → Fin n → Fin m → Bool
x <b zero = false
zero <b suc y = true
suc x <b suc y = x <b y

mutual
  shift : ∀ {i I} → Fin (suc i) → Codeᵍ I i → Codeᵍ I (suc i)
  shift d (ins ▸ᵍ c) = shiftCont d ins  ▸ᵍ shift d c
  shift d HALTᵍ = HALTᵍ
  shift d (LABᵍ→ c1 c2) = LABᵍ→ (shift (suc d) c1) (shift d c2)
  shift d (LABᵍ← c) = LABᵍ← (shift (suc d) c)
  shift d (JMPᵍ x) = JMPᵍ (shiftVar d x)

  shiftCont : ∀ {i n I} → Fin (suc i) → Cont I (Fin i) n → Cont I (Fin (suc i)) n
  shiftCont d (x !) = x !
  shiftCont d (c ＠ x) = shiftCont d c ＠ (shiftVar d x)

  shiftVar : ∀ {i} → Fin (suc i) → Fin i → Fin (suc i)
  shiftVar d v = if v <b d then inject₁ v else suc v

⇑_ : ∀ {i I} → Codeᵍ I i → Codeᵍ I (suc i)
⇑ c = shift zero c

POPAt : ∀ {A : Set} {n} → Vec A (suc n) → Fin (suc n) → Vec A n
POPAt (x ∷ v) zero = v
POPAt {n = suc n} (x ∷ v) (suc i) = x ∷ POPAt v i


data _e≈[_]_  {I : ℕ → Set} : ∀ {n} → Vec (Code I ∞) n → Size → Vec (Code I ∞) n → Set where
  ≈nil : ∀ {i} → [] e≈[ i ] []
  ≈cons : ∀ {n i c d} {cs ds : Vec _ n} → c ≈[ i ] d → cs e≈[ i ] ds → (c ∷ cs) e≈[ i ] (d ∷ ds)

e≈refl : ∀{i I n} {e : Vec (Code I ∞) n} → e e≈[ i ] e
e≈refl {e = []} = ≈nil
e≈refl {e = x ∷ e} = ≈cons ≈refl e≈refl

e≈down : ∀{i I n} {e e' : Vec (Code I ∞) n} {j : Size< (↑ i)} → e e≈[ i ] e' → e e≈[ j ] e'
e≈down ≈nil = ≈nil
e≈down (≈cons x bi) = ≈cons (≈down x) (e≈down bi)


≈lookup : ∀ {i I n} {es es' : Vec (Code I ∞) n} x → es e≈[ i ] es' → lookup es x ≈[ i ] lookup es' x
≈lookup zero (≈cons bi bis) = bi
≈lookup (suc x) (≈cons bi bis) = ≈lookup x bis


mutual
  unravel-e≈ : ∀ {i I n es es'} (c : Codeᵍ I n) → es e≈[ i ] es' → ⦅ c ⦆ es ≈[ i ] ⦅ c ⦆ es'
  unravel-e≈ (x ▸ᵍ c) bi = ≈▸ (unravI-e≈ x bi) (unravel-e≈ c bi)
  unravel-e≈ HALTᵍ bi = ≈refl
  unravel-e≈ (LABᵍ→ c c') bi = unravel-e≈ c (≈cons (unravel-e≈ c' bi) bi)
  unravel-e≈ (LABᵍ← c) bi = unravel-e≈ c (≈cons (≈REC (∞unravel-e≈ (LABᵍ← c) bi)) bi)
  unravel-e≈ (JMPᵍ x) bi = ≈lookup x bi

  unravI-e≈ : ∀ {i I m n es es'} (c : Cont I (Fin n) m) → es e≈[ i ] es' → unravI c es c≈[ i ] unravI c es'
  unravI-e≈ (x !) bi = ≈!
  unravI-e≈ (c ＠ x) bi = ≈＠ (unravI-e≈ c bi) (≈lookup x bi)

  ∞unravel-e≈ : ∀ {i I n es es'} (c : Codeᵍ I n) → es e≈[ i ] es' → ∞⦅ c ⦆ es ∞≈[ i ] ∞⦅ c ⦆ es'
  ≈force (∞unravel-e≈ c bi) {j} = unravel-e≈ {j} c (e≈down bi)


shiftVar-suc : ∀ {n} d (x : Fin n) → shiftVar (suc d) (suc x) ≡ suc (shiftVar d x)
shiftVar-suc d x with (x <b d)
... | false = refl
... | true = refl

lookup-shift : ∀ {n A} (e : Vec A (suc n)) d x → lookup (POPAt e d) x ≡ lookup e (shiftVar d x)
lookup-shift (y ∷ ys) zero zero = refl
lookup-shift (y ∷ ys) (suc d) zero = refl
lookup-shift (y ∷ ys) zero (suc x) = refl
lookup-shift (y ∷ ys) (suc d) (suc x) rewrite shiftVar-suc d x = lookup-shift ys d x


mutual
  unravel-shift : ∀ {i n I} (c : Codeᵍ I n) (e : Vec (Code I ∞) (suc n)) (d : Fin (suc n))
    → ⦅ c ⦆ (POPAt e d) ≈[ i ] ⦅ shift d c ⦆ e
  unravel-shift (ins ▸ᵍ c) e d = ≈▸ (unravI-shift ins e d) (unravel-shift c e d)
  unravel-shift HALTᵍ e d = ≈refl
  unravel-shift (LABᵍ→ c c') e d =
    ≈trans (unravel-e≈ c (≈cons (unravel-shift c' e d) e≈refl))
    (unravel-shift c (⦅ shift d c' ⦆ e ∷ e) (suc d))
  unravel-shift (LABᵍ← c) e d = ≈trans (unravel-e≈ c (≈cons (≈REC (∞unravel-shift (LABᵍ← c) e d)) e≈refl)) (unravel-shift c _ (suc d))
  unravel-shift (JMPᵍ x) e d rewrite lookup-shift e d x =  ≈refl

  ∞unravel-shift : ∀ {i n I} (c : Codeᵍ I n) (e : Vec (Code I ∞) (suc n)) (d : Fin (suc n))
    → ∞⦅ c ⦆ (POPAt e d) ∞≈[ i ] ∞⦅ shift d c ⦆ e
  ≈force (∞unravel-shift c e d) = unravel-shift c e d

  unravI-shift : ∀ {i n I m} (c : Cont I (Fin n) m) (e : Vec (Code I ∞) (suc n)) (d : Fin (suc n))
    → unravI c (POPAt e d) c≈[ i ] unravI (shiftCont d c) e
  unravI-shift (x !) e d = ≈!
  unravI-shift (c ＠ x) e d rewrite lookup-shift e d x = ≈＠ (unravI-shift c e d) ≈refl
    
unravel⇑ : ∀ {i n I} (c : Codeᵍ I n) (e : Vec (Code I ∞) n) (a : Code I ∞) → ⦅ c ⦆ e ≈[ i ] ⦅ ⇑ c  ⦆ (a ∷ e)
unravel⇑ c e a = unravel-shift c (a ∷ e) zero

----------------------------------------- 
-- Linearise graphs to sequential code --
----------------------------------------- 


data SeqnElem (I : ℕ → Set) : Set where
  DO : Cont I ℕ 0 → SeqnElem I
  JMPₛ : ℕ → SeqnElem I
  HALTₛ : SeqnElem I

Seqn : (I : ℕ → Set) → Set
Seqn I = List (SeqnElem I)

lengthᵍ : ∀ {I n} → Codeᵍ I n → ℕ → ℕ
lengthᵍ (x ▸ᵍ c) a = lengthᵍ c (suc a)
lengthᵍ HALTᵍ a = suc a
lengthᵍ (LABᵍ→ f c) a = lengthᵍ c (lengthᵍ f a)
lengthᵍ (LABᵍ← x) a = lengthᵍ x a
lengthᵍ (JMPᵍ x) a = suc a


seqn' : ∀ {I n} → Codeᵍ I n → Vec ℕ n → ℕ → Seqn I
seqn' (x ▸ᵍ c) e l = DO (mapC (lookup e) x) ∷ seqn' c e (suc l)
seqn' HALTᵍ e l = [ HALTₛ ]
seqn' (LABᵍ→ f c) e l =
  let l' = lengthᵍ f l
  in seqn' f (l' ∷ e) l ++ seqn' c e l'
seqn' (LABᵍ← x) e l = seqn' x (l ∷ e) l
seqn' (JMPᵍ x) e l = [ JMPₛ (lookup e x) ]


seqn : ∀ {I} → Codeᵍ I 0 → Seqn I
seqn c = seqn' c [] 0