module induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import addition-associativity using (+-assoc)


+-idr : ∀ (a : ℕ) → a + zero ≡ a
+-idr zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-idr (suc a) =
  begin
    suc a + zero
  ≡⟨⟩
    suc (a + zero)
  ≡⟨ cong suc (+-idr a) ⟩
    suc a
  ∎

+-idl : ∀ (a : ℕ) → zero + a ≡ a
+-idl zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-idl (suc a) =
  begin
    zero + (suc a)
  ≡⟨⟩
    suc (zero + a)
  ≡⟨ cong suc (+-idl a) ⟩
    suc a
  ∎

+-suc : ∀ (a b : ℕ) → a + suc b ≡ suc (a + b)
+-suc zero b =
  begin
    zero + suc b
  ≡⟨⟩
    suc b
  ≡⟨⟩
    suc (zero + b)
  ∎
+-suc (suc a) b =
  begin
    suc a + suc b
  ≡⟨⟩
    suc (a + suc b)
  ≡⟨ cong suc (+-suc a b) ⟩
    suc (suc (a + b))
  ≡⟨⟩
    suc (suc a + b)
  ∎

+-commutes : ∀ (a b : ℕ) → a + b ≡ b + a
+-commutes b zero =
  begin
    b + zero
  ≡⟨ +-idr b ⟩
    b
  ≡⟨⟩
    zero + b
  ∎
+-commutes a (suc b) =
  begin
    a + (suc b)
  ≡⟨ +-suc a b ⟩
    suc (a + b)
  ≡⟨ cong suc (+-commutes a b) ⟩
    suc (b + a)
  ≡⟨⟩
    suc b + a
  ∎
