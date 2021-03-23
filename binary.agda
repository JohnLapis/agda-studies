module binary where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; suc; _*_; _+_)
open import induction using (+-suc-r; *-commutes)

-- Binary representation of integer

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to 0 = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (x O) = 2 * (from x)
from (x I) = 1 + 2  * (from x)


inc-is-bin-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc-is-bin-suc ⟨⟩ = refl
inc-is-bin-suc (x O) = refl
inc-is-bin-suc (x I) =
  begin
    from (inc (x I))
  ≡⟨⟩
    from ((inc x) O)
  ≡⟨⟩
    2 * from (inc x)
  ≡⟨ cong (2 *_) (inc-is-bin-suc x) ⟩
    2 * suc (from x)
  ≡⟨ *-commutes 2 (suc (from x)) ⟩
    suc (from x) * 2
  ≡⟨⟩
    2 + from x * 2
  ≡⟨ cong (2 +_) (*-commutes (from x) 2) ⟩
    2 + 2 * from x
  ≡⟨⟩
    2 + from (x O)
  ≡⟨⟩
    suc 1 + from (x O)
  ≡⟨⟩
    suc (1 + from (x O))
  ≡⟨⟩
    suc (from (x I))
  ∎

-- to-is-inv-from : ∀ (b : Bin) → to (from b) ≡ b
-- to-is-inv-from = to (from (⟨⟩ O O)) ≡ ⟨⟩ O != ⟨⟩ O O

from-is-inv-to : ∀ (n : ℕ) → from (to n) ≡ n
from-is-inv-to 0 = refl
from-is-inv-to (suc n) =
  begin
    from (inc (to n))
  ≡⟨ inc-is-bin-suc (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (from-is-inv-to n) ⟩
    suc n
  ∎
