module equality where


-- ≤-Reasoning
-- The proof of monotonicity from Chapter Relations can be written in a more
-- readable form by using an analogue of our notation for ≤-Reasoning. Define
-- ≤-Reasoning analogously, and use it to write out an alternative proof that
-- addition is monotonic with regard to inequality. Rewrite all of +-monoˡ-≤,
-- +-monoʳ-≤, and +-mono-≤.

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

data _≤_ {A : Set} (x : A) : A → Set where
  refl : x ≤ x

infix 4 _≤_

sym : ∀ {A : Set} {x y : A}
  → x ≤ y
    -----
  → y ≤ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≤ y
  → y ≤ z
    -----
  → x ≤ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≤ y
    ---------
  → f x ≤ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≤ x
  → v ≤ y
    -------------
  → f u v ≤ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≤ g
    ---------------------
  → ∀ (x : A) → f x ≤ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≤ y
    ---------
  → P x → P y
subst P refl px = px

module ≤-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≤ y
      -----
    → x ≤ y
  begin x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : A) {y : A}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = trans x≤y y≤z

  _∎ : ∀ (x : A)
      -----
    → x ≤ x
  x ∎ = refl

open ≤-Reasoning

postulate
  +-comm : ∀ (n m : ℕ) → n + m ≤ m + n

{-# BUILTIN EQUALITY _≤_ #-}

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q refl  =  refl
+-monoʳ-≤ (suc n) p q refl  =  cong suc (+-monoʳ-≤ n p q refl)

+-monoˡ-≤ : ∀ (n p q : ℕ)
  → n ≤ p
    -------------
  → n + q ≤ p + q
+-monoˡ-≤ n p q refl rewrite +-comm n q | +-comm p q = +-monoʳ-≤ q n p refl

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q refl refl = trans (+-monoˡ-≤ m n p refl) (+-monoʳ-≤ n p q refl)
