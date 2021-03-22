module induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import addition-associativity using (+-assoc)


-- Addion proofs

+-identity-r : ∀ (a : ℕ) → a + zero ≡ a
+-identity-r zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identity-r (suc a) =
  begin
    suc a + zero
  ≡⟨⟩
    suc (a + zero)
  ≡⟨ cong suc (+-identity-r a) ⟩
    suc a
  ∎

+-suc-r : ∀ (a b : ℕ) → a + suc b ≡ suc (a + b)
+-suc-r zero b = refl
+-suc-r (suc a) b =
  begin
    suc a + suc b
  ≡⟨⟩
    suc (a + suc b)
  ≡⟨ cong suc (+-suc-r a b) ⟩
    suc (suc (a + b))
  ≡⟨⟩
    suc (suc a + b)
  ∎

+-commutes : ∀ (a b : ℕ) → a + b ≡ b + a
+-commutes b 0 =
  begin
    b + 0
  ≡⟨ +-identity-r b ⟩
    b
  ≡⟨⟩
    0 + b
  ∎
+-commutes a (suc b) =
  begin
    a + (suc b)
  ≡⟨ +-suc-r a b ⟩
    suc (a + b)
  ≡⟨ cong suc (+-commutes a b) ⟩
    suc (b + a)
  ≡⟨⟩
    suc b + a
  ∎

+-assoc-r : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc-r 0 b c = refl
+-assoc-r (suc a) b c rewrite +-assoc-r a b c = refl


-- Multiplication proofs

*-identity-l : ∀ (n : ℕ) → 1 * n ≡ n
*-identity-l zero = refl
*-identity-l (suc n) rewrite *-identity-l n = refl

*-identity-r : ∀ (n : ℕ) → n * 1 ≡ n
*-identity-r zero = refl
*-identity-r (suc n) rewrite *-identity-r n = refl

*-zero-r : ∀ (n : ℕ) → n * 0 ≡ 0
*-zero-r 0 = refl
*-zero-r (suc n) rewrite *-zero-r n = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ 0 n p =
  begin
    (0 + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    0 * p + n * p
  ∎
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ +-assoc p (m * p) (n * p) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    (suc m * p) + (n * p)
  ∎

*-commutes : ∀ (n m : ℕ) → n * m ≡ m * n
*-commutes 0 m =
  begin
    0 * m
  ≡⟨⟩
    0
  ≡⟨ sym (*-zero-r m) ⟩
    m * 0
  ∎
*-commutes (suc n) 0 rewrite *-commutes n 0 = refl
*-commutes (suc n) (suc m) =
  begin
    suc n * suc m
  ≡⟨⟩
    suc m + n * suc m
  ≡⟨ cong (suc m +_) (*-commutes n (suc m)) ⟩
    suc m + suc m * n
  ≡⟨⟩
    suc m + (n + m * n)
  ≡⟨ +-assoc (suc m) n (m * n) ⟩
    suc m + n + m * n
  ≡⟨⟩
    suc (m + n) + m * n
  ≡⟨ cong (_+ m * n) (sym (+-suc-r m n)) ⟩
    m + suc n + m * n
  ≡⟨ cong (_+ m * n) (+-commutes m (suc n)) ⟩
    suc n + m + m * n
  ≡⟨ cong ((suc n + m) +_) (*-commutes m n) ⟩
    suc n + m + n * m
  ≡⟨ +-assoc-r (suc n) m (n * m) ⟩
    suc n + (m + n * m)
  ≡⟨⟩
    suc n + suc n * m
  ≡⟨ cong (suc n +_) (*-commutes (suc n) m) ⟩
    suc n + m * suc n
  ≡⟨⟩
    suc m * suc n
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc 0 n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl


-- Monus proofs

∸-zero-l : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-zero-l 0 = refl
∸-zero-l (suc n) rewrite ∸-zero-l n = refl

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc m 0 p = refl
∸-|-assoc 0 (suc n) p rewrite ∸-zero-l p = refl
∸-|-assoc (suc m) (suc n) p rewrite ∸-|-assoc m n p = refl


-- Exponentiation proofs

^-distrib-l-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distrib-l-|-* m 0 p rewrite *-identity-l (m ^ p) = refl
^-distrib-l-|-* m (suc n) p =
  begin
    m ^ (suc n + p)
  ≡⟨ cong (m *_) (^-distrib-l-|-* m n p) ⟩
    m * (m ^ n * m ^ p)
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m ^ suc n * m ^ p
  ∎

^-distrib-r-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distrib-r-* m n 0 = refl
^-distrib-r-* m n (suc p) =
  begin
    (m * n) ^ suc p
  ≡⟨ cong (m * n *_) (^-distrib-r-* m n p) ⟩
    m * n * (m ^ p * n ^ p)
  ≡⟨ *-assoc m n (m ^ p * n ^ p) ⟩
    m * (n * (m ^ p * n ^ p))
  ≡⟨ cong (m *_) (*-commutes n (m ^ p * n ^ p)) ⟩
    m * ((m ^ p * n ^ p) * n)
  ≡⟨ cong (m *_) (*-assoc (m ^ p) (n ^ p) n) ⟩
    m * (m ^ p * (n ^ p * n))
  ≡⟨ sym (*-assoc m (m ^ p) (n ^ p * n)) ⟩
    (m ^ suc p) * (n ^ p * n)
  ≡⟨ cong (m ^ suc p *_) (*-commutes (n ^ p) n) ⟩
    (m ^ suc p) * (n ^ suc p)
  ∎

^-*-commutes : ∀ (m n p : ℕ) → m ^ (n * p) ≡ m ^ (p * n)
^-*-commutes m n p rewrite *-commutes n p = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n 0 rewrite *-zero-r n = refl
^-*-assoc m n (suc p) =
  begin
    (m ^ n) ^ suc p
  ≡⟨ cong (m ^ n *_) (^-*-assoc m n p) ⟩
    (m ^ n) * (m ^ (n * p))
  ≡⟨ cong (m ^ n *_) (^-*-commutes m n p) ⟩
    (m ^ n) * (m ^ (p * n))
  ≡⟨ sym (^-distrib-l-|-* m n (p * n)) ⟩
    m ^ (suc p * n)
  ≡⟨ cong (m ^_) (*-commutes (suc p) n) ⟩
    m ^ (n * suc p)
  ∎
