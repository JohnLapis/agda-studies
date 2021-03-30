{-# OPTIONS --allow-unsolved-metas #-}
module relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)


data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
    → zero ≤ n
  s≤s : ∀ {n m : ℕ}
    → m ≤ n
    → suc m ≤ suc n

infix 4 _≤_

+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {n : ℕ}
  → n ≤ zero
    -------------
  → n ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)


data Total (m n : ℕ) : Set where
  forward :
      m ≤ n
      ---------
    → Total m n
  flipped :
      n ≤ m
      ---------
    → Total m n


≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero _ = forward z≤n
≤-total _ zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                          | forward m≤n = forward (s≤s m≤n)
...                          | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (n p q : ℕ)
  → n ≤ p
    -------------
  → n + q ≤ p + q
+-monoˡ-≤ n p q n≤p rewrite +-comm n q | +-comm p q = +-monoʳ-≤ q n p n≤p

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-mono-≤ʳ : ∀ (a b c : ℕ)
  → b ≤ c
  ---------------
  → a * b ≤ a * c
*-mono-≤ʳ zero b c b≤c = z≤n
*-mono-≤ʳ (suc a) b c b≤c = +-mono-≤ b c (a * b) (a * c) b≤c (*-mono-≤ʳ a b c b≤c)

*-mono-≤ˡ : ∀ (a b c : ℕ)
  → a ≤ b
  ---------------
  → a * c ≤ b * c
*-mono-≤ˡ a b c a≤b rewrite *-comm a c | *-comm b c = *-mono-≤ʳ c a b a≤b

*-mono-≤ : ∀ (a b c d : ℕ)
  → a ≤ c
  → b ≤ d
  ---------------
  → a * b ≤ c * d
*-mono-≤ a b c d a≤c b≤d = ≤-trans (*-mono-≤ˡ a c b a≤c) (*-mono-≤ʳ c b d b≤d)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n


<-trans : ∀ {a b c : ℕ}
  → a < b
  → b < c
  -------
  → a < c
<-trans z<s (s<s b<c) = z<s
<-trans  (s<s a<b) (s<s b<c) = s<s (<-trans a<b b<c)

suc-≤-to-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
suc-≤-to-< zero zero ()
suc-≤-to-< zero (suc n) m≤n = z<s
suc-≤-to-< (suc m) (suc n) (s≤s m≤n) = s<s (suc-≤-to-< m n m≤n)

data Trichotomy (m n : ℕ) : Set where
  eq : m ≡ n → Trichotomy m n
  lt : m < n → Trichotomy m n
  gt : n < m → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = eq refl
<-trichotomy zero (suc n) = lt z<s
<-trichotomy (suc m) zero = gt z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                               | lt m<n = lt (s<s m<n)
...                               | gt n<m = gt (s<s n<m)
...                               | eq m≡n = eq (cong suc m≡n)


-- Show that addition is monotonic with respect to strict inequality. As with
-- inequality, some additional definitions may be required.
+-monoˡ-< : ∀ (a b c : ℕ)
  → a < b
  -------
  → a + c < b + c
+-monoˡ-< = {!!}

+-monoʳ-< : ∀ (a b c : ℕ)
  → b < c
  -------
  → a + b < a + c
+-monoʳ-< = {!!}

+-mono-< : ∀ (a b c d : ℕ)
  → a < c
  → b < d
  -------
  → a + b < c + d
+-mono-< a b c d a<c b<d = <-trans (+-monoˡ-< a c b a<c) (+-monoʳ-< c b d b<d)

<-to-suc-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-to-suc-≤ z<s = s≤s z≤n
<-to-suc-≤ (s<s m<n) = s≤s (<-to-suc-≤ m<n)

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    -----------
  → odd (m + n)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    -----------
  → even (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

e+o≡o zero on = on
e+o≡o (suc om) on = suc (o+o≡e om on)

o+o≡e (suc em) on = suc (e+o≡o em on)
