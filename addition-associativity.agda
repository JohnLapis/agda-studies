module addition-associativity where

open import Data.Nat using (ℕ; _+_; zero; suc)
open import Relation.Binary.PropositionalEquality using (refl; cong; _≡_)

+-assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-assoc zero y z = refl
+-assoc (suc x) y z = cong suc (+-assoc x y z)
